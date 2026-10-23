-- Prove2me | Definitions.Def_MNLTrisection_Adaptive_Model
-- name    : MNLTrisection_Adaptive_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:27.173554+00:00
-- url     : https://prove2.me/theorems/9fe2d72a-1ccf-4fdd-97f0-a74be941449a
-- title:
--   §3–§6, pp. 6–13 — level sets, the revenue potential F, F*, θ*, the adaptive trisection policy (Algorithms 1–2 with (12)), epochs, ℰ_ω(τ) and ψ^ω_τ(α, β) of (14)
-- statement:
--   This file sets up the dynamic assortment problem of Chen, Wang and Zhou under the uncapacitated multinomial logit (MNL) model, the adaptive-confidence trisection policy, and the quantities used in its regret analysis.
--
--   **Model** (§3, p. 6). There are $N$ items with known revenues $r_1,\dots,r_N$ and unknown utilities $v_1,\dots,v_N \ge 0$; the no-purchase option has utility $v_0 = 1$. Every subset $S \subseteq [N]$ is an admissible assortment. A customer offered $S$ buys $j \in S$ with probability $v_j/(1+\sum_{i\in S} v_i)$ and nothing with probability $1/(1+\sum_{i\in S} v_i)$, and the expected revenue of $S$ is
--   $$R(S) = \frac{\sum_{j\in S} r_j v_j}{1+\sum_{j\in S} v_j}.$$
--   The choice model, histories, deterministic policies, the law of a purchase history and the regret $T\max_{S} R(S) - \mathbb E\sum_{t=1}^T R(S_t)$ are those of the published `MNLBandit.UCB.Setting`, taken with the family of all subsets. $R(S^*) = \max_{S \subseteq [N]} R(S)$ is the optimal revenue.
--
--   **Potential** (§4, pp. 7–8). The $\theta$-level set is $\mathcal L_\theta = \{i : r_i \ge \theta\}$ and the revenue potential is $F(\theta) = R(\mathcal L_\theta)$, defined for every real $\theta$. $F^* = \sup_{\theta \ge 0} F(\theta)$, and $\theta^*$ denotes $F^*$ (Lemma 2 shows that the fixed point $\theta^* = F(\theta^*) = F^*$ of the paper has this value).
--
--   **Policy** (Algorithms 1–2, p. 9, with the changes of p. 12). The policy knows $r$ and $T$ but not $v$. It starts with $a_0 = 0$, $b_0 = 1$. In outer iteration (epoch) $\tau$ it sets $x_\tau = \tfrac23 a_\tau + \tfrac13 b_\tau$, $y_\tau = \tfrac13 a_\tau + \tfrac23 b_\tau$, $\rho_0 = 0$, $\ell_0 = 0$, $u_0 = 1$, and runs inner iterations $t = 1, \dots, n_\tau$ with
--   $$n_\tau = 8\Big\lceil (y_\tau - x_\tau)^{-2}\ln\big(8T(y_\tau-x_\tau)^2\big)\Big\rceil .$$
--   In inner iteration $t$: if $\ell_{t-1} \le y_\tau \le u_{t-1}$, the level set $\mathcal L_{y_\tau}$ is offered to one customer, whose purchase $j$ (with $r_0 := 0$) updates $\rho_t = \rho_{t-1} + r_j$ and
--   $$[\ell_t, u_t] = \frac{\rho_t}{t} \pm \sqrt{\frac{2\ln(8T/t)}{t}}$$
--   (the confidence interval (12) with $\delta = 1/T$); otherwise $\rho, \ell, u$ are carried over. Then $\mathcal L_{a_\tau}$ is offered to the next customer. After inner iteration $n_\tau$: if $u < y_\tau$ then $a_{\tau+1} = a_\tau$, $b_{\tau+1} = y_\tau$, else $a_{\tau+1} = x_\tau$, $b_{\tau+1} = b_\tau$. The run stops after $T$ customers. Every epoch shrinks $[a_\tau, b_\tau]$ by a factor $2/3$, so $y_\tau - x_\tau = \varepsilon_\tau := \tfrac13(\tfrac23)^\tau$ and $n_\tau$ depends on $T$ and $\tau$ only.
--
--   **Epochs along a history.** For a purchase history $h$ of length $T$: the epoch of each period, $\mathcal T(\tau)$ (the periods of epoch $\tau$), $\tau_0$ (the last epoch), $a_\tau, b_\tau$ (the interval of epoch $\tau$ when it starts), and $\bar\tau(T) = \max\{\tau : \sum_{\tau'<\tau} n_{\tau'} < T\}$, the last epoch that can start.
--
--   **Events and conditional regrets** ((14), pp. 12–13). On histories where epoch $\tau$ starts, $\mathcal E_1(\tau) : \theta^* < a_\tau < b_\tau$, $\mathcal E_2(\tau) : a_\tau \le \theta^* \le b_\tau$, $\mathcal E_3(\tau) : a_\tau < b_\tau < \theta^*$, and for $\omega \in \{1,2,3\}$, $\alpha, \beta \ge 0$,
--   $$\psi^\omega_\tau(\alpha,\beta) = \mathbb E\Big[\sum_{\tau'=\tau}^{\tau_0}\sum_{t\in\mathcal T(\tau')} R(S^*) - R(S_t)\ \Big|\ \mathcal E_\omega(\tau),\ |a_\tau - \theta^*| = \alpha,\ |F(a_\tau) - a_\tau| = \beta\Big].$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Items are `Fin N` (the paper's item $i$ is index $i-1$) and periods are 0-based; epochs and the inner index $t$ are as on the page. $F$ is defined on all of $\mathbb R$ so that the right limit $F(\theta^+)$ is Mathlib's `Function.rightLim`. The inner-iteration count is $\max(1, n_\tau)$: the printed $n_\tau$ is $0$ only for tiny $T$ (e.g. $T = 1$), where an epoch without inner iterations would never end. The empty assortment is allowed (it is $\mathcal L_\theta$ for $\theta > \max_i r_i$; $R(\varnothing) = 0$), whereas §3 asks $S_t \neq \varnothing$. The policy state is recomputed from the observed choices by folding a one-period update; an epoch change is processed right after the last customer of the epoch, so every period belongs to exactly one epoch. The conditional expectation $\psi$ is a ratio of finite sums over histories and is $0$ when the conditioning event has probability $0$. $\theta^*$ is defined as $F^*$.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, pp. 6–13, §3 (1)–(3), §4 (4)–(5), Algorithms 1–2 (p. 9), the variant and (12) (p. 12), §6.1 events and (14) (pp. 12–13)

import Mathlib
import Definitions.Def_MNLBandit_UCB_Setting

namespace MNLTrisection.Adaptive

open MNLBandit.UCB ChoiceCDLP.MNL

/-!
Chen, Wang & Zhou, *An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated
Multinomial Logit Models*, arXiv:1805.04785v2.

The model of §3 (p. 6) is the published `MNLBandit.UCB.Setting` with the family of all
assortments `𝒮 = Finset.univ` (`𝕊 = 2^𝒩`). This file adds the level sets and the revenue
potential of §4 (pp. 7–8), the adaptive-confidence variant of the trisection policy
(Algorithms 1–2 on p. 9 with the two changes of p. 12), its epochs along a purchase history, the
events `ℰ_ω(τ)` and the conditional regrets `ψ^ω_τ(α, β)` of (14) (pp. 12–13).
-/

/-- The expected revenue (2), `R(S) = ∑_{j ∈ S} r_j v_j / (1 + ∑_{j ∈ S} v_j)`, with `v₀ = 1`. -/
noncomputable def rev {N : ℕ} (v r : Fin N → ℝ) (S : Finset (Fin N)) : ℝ :=
  mnlObjective v r 1 S

/-- The optimal revenue `R(S*) = max_{S ⊆ [N]} R(S)` over all assortments (3). -/
noncomputable def optRev {N : ℕ} (v r : Fin N → ℝ) : ℝ :=
  optRevenue v r (Finset.univ : Finset (Finset (Fin N))) ⟨∅, Finset.mem_univ _⟩

/-- The `θ`-level set `𝓛_θ = {i : r_i ≥ θ}` (p. 7). -/
noncomputable def levelSet {N : ℕ} (r : Fin N → ℝ) (θ : ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => θ ≤ r i)

/-- The revenue potential (5), `F(θ) = R(𝓛_θ)`, defined for every real `θ`. -/
noncomputable def F {N : ℕ} (v r : Fin N → ℝ) (θ : ℝ) : ℝ :=
  rev v r (levelSet r θ)

/-- `F* = sup_{θ ≥ 0} F(θ)` (p. 8). `F` takes finitely many values, so the supremum is a
maximum of a nonempty finite set. -/
noncomputable def Fstar {N : ℕ} (v r : Fin N → ℝ) : ℝ :=
  sSup (F v r '' Set.Ici 0)

/-- The fixed point `θ*` of Lemmas 2–4 and 9–11. Lemma 2 forces `θ* = F*`; this is the
definition used. -/
noncomputable def thetaStar {N : ℕ} (v r : Fin N → ℝ) : ℝ :=
  Fstar v r

/-! ### Parameters of the adaptive-confidence variant (p. 12) -/

/-- `ε_τ = y_τ − x_τ = (1/3)(2/3)^τ`, the distance between the trisection points of epoch `τ`
(every epoch shrinks `[a_τ, b_τ]` to two thirds of its length, starting from `[0, 1]`). -/
noncomputable def eps (τ : ℕ) : ℝ :=
  (1 / 3) * (2 / 3) ^ τ

/-- The number of inner iterations for trisection gap `e = y − x`:
`max(1, 8⌈e^{-2} ln(8 T e²)⌉)`. The printed value is `8⌈(y_τ − x_τ)^{-2} ln(8T(y_τ − x_τ)²)⌉`;
`max 1` only matters when the printed value is `0` (e.g. `T = 1`). -/
noncomputable def innerLen (T : ℕ) (e : ℝ) : ℕ :=
  max 1 (8 * ⌈e⁻¹ ^ 2 * Real.log (8 * (T : ℝ) * e ^ 2)⌉₊)

/-- `n_τ = max(1, 8⌈ε_τ^{-2} ln(8Tε_τ²)⌉)`, the number of inner iterations of epoch `τ`. -/
noncomputable def nEpoch (T τ : ℕ) : ℕ :=
  innerLen T (eps τ)

/-- The confidence radius (12) with `δ = 1/T` at inner iteration `t`:
`√(2 ln[8/(δt)]/t) = √(2 ln(8T/t)/t)`. -/
noncomputable def radius (T t : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log (8 * (T : ℝ) / t) / t)

/-! ### The policy -/

/-- The internal state of the variant of Algorithm 1 between two periods.
* `tau` — the current outer iteration `τ`;
* `a`, `b` — the trisection interval `[a_τ, b_τ]`;
* `k` — the number of inner iterations of epoch `τ` already completed;
* `rho`, `lo`, `up` — `ρ_k(y_τ)`, `ℓ_k(y_τ)`, `u_k(y_τ)`;
* `explored` — `true` iff the exploration step of inner iteration `k + 1` has been carried out
  and its exploitation step is next. -/
structure AlgState where
  tau : ℕ
  a : ℝ
  b : ℝ
  k : ℕ
  rho : ℝ
  lo : ℝ
  up : ℝ
  explored : Bool

/-- `x_τ = (2/3) a_τ + (1/3) b_τ` (line 3 of Algorithm 1). -/
noncomputable def AlgState.x (s : AlgState) : ℝ := 2 / 3 * s.a + 1 / 3 * s.b

/-- `y_τ = (1/3) a_τ + (2/3) b_τ` (line 3 of Algorithm 1). -/
noncomputable def AlgState.y (s : AlgState) : ℝ := 1 / 3 * s.a + 2 / 3 * s.b

/-- The start of epoch `τ` with interval `[a, b]`: `ℓ₀(y) = 0`, `u₀(y) = 1`, `ρ₀(y) = 0`
(lines 4–5 of Algorithm 1). -/
def epochStart (τ : ℕ) (a b : ℝ) : AlgState :=
  ⟨τ, a, b, 0, 0, 0, 1, false⟩

/-- The initial state: `a₀ = 0`, `b₀ = 1` (line 1 of Algorithm 1). -/
def initState : AlgState := epochStart 0 0 1

/-- The next period is an exploration of `𝓛_{y_τ}` (line 7 of Algorithm 1): the exploration
step of the current inner iteration has not been done yet and `ℓ_{t−1}(y_τ) ≤ y_τ ≤ u_{t−1}(y_τ)`. -/
def AlgState.exploreNow (s : AlgState) : Prop :=
  s.explored = false ∧ s.lo ≤ s.y ∧ s.y ≤ s.up

/-- The assortment offered in state `s`: `𝓛_{y_τ}` for an exploration (Algorithm 2, step 1),
and otherwise the exploitation `𝓛_{a_τ}` (line 9 of Algorithm 1). -/
noncomputable def offerOf {N : ℕ} (r : Fin N → ℝ) (s : AlgState) : Finset (Fin N) := by
  classical
  exact if s.exploreNow then levelSet r s.y else levelSet r s.a

/-- The revenue `r_j` of the purchase `j`, with `r₀ := 0` for no purchase. -/
def choiceRev {N : ℕ} (r : Fin N → ℝ) : Option (Fin N) → ℝ
  | none => 0
  | some j => r j

/-- The state after observing the choice `c` of the customer served in state `s`.
* Exploration (Algorithm 2 with (12), `δ = 1/T`): at inner iteration `t = k + 1`,
  `ρ_t = ρ_{t−1} + r_j` and `[ℓ_t, u_t] = ρ_t/t ± √(2 ln(8T/t)/t)`; the exploitation of the same
  inner iteration comes next.
* Exploitation (line 9): inner iteration `k + 1` is completed (when exploration was inactive,
  line 8 carried `ρ, ℓ, u` over). After inner iteration `n_τ = max(1, 8⌈(y_τ − x_τ)^{-2}
  ln(8T(y_τ − x_τ)²)⌉)`, the trisection parameters are updated (lines 11–12): if `u(y_τ) < y_τ`
  then `a_{τ+1} = a_τ`, `b_{τ+1} = y_τ`, else `a_{τ+1} = x_τ`, `b_{τ+1} = b_τ`, and epoch `τ + 1`
  starts. -/
noncomputable def step {N : ℕ} (r : Fin N → ℝ) (T : ℕ) (s : AlgState) (c : Option (Fin N)) :
    AlgState := by
  classical
  exact
    if s.exploreNow then
      let t : ℕ := s.k + 1
      let ρ' := s.rho + choiceRev r c
      { s with rho := ρ', lo := ρ' / t - radius T t, up := ρ' / t + radius T t,
               explored := true }
    else
      if innerLen T (s.y - s.x) ≤ s.k + 1 then
        (if s.up < s.y then epochStart (s.tau + 1) s.a s.y
         else epochStart (s.tau + 1) s.x s.b)
      else
        { s with k := s.k + 1, explored := false }

/-- The state of the algorithm before period `t` (0-based), after the choices `p` of the
customers `0, …, t − 1`. -/
noncomputable def stateAt {N : ℕ} (r : Fin N → ℝ) (T t : ℕ) (p : Fin t → Option (Fin N)) :
    AlgState :=
  (List.ofFn p).foldl (step r T) initState

/-- **The adaptive-confidence trisection policy** (the variant of Algorithm 1 on p. 12) for
horizon `T`. It is a function of the known revenues `r`, the horizon `T` and the observed choices
only; it never sees the utilities `v`. -/
noncomputable def adaptivePolicy {N : ℕ} (r : Fin N → ℝ) (T : ℕ) : Policy N :=
  fun t p => offerOf r (stateAt r T t p)

/-! ### Epochs along a history -/

/-- The algorithm's state before period `t` along the history `h`. -/
noncomputable def stateOf {N T : ℕ} (r : Fin N → ℝ) (h : History N T) (t : Fin T) : AlgState :=
  stateAt r T t.val (histPrefix h t)

/-- The outer iteration (epoch) to which period `t` belongs. -/
noncomputable def epochOf {N T : ℕ} (r : Fin N → ℝ) (h : History N T) (t : Fin T) : ℕ :=
  (stateOf r h t).tau

/-- Epoch `τ` starts along `h`: some period belongs to it. -/
def Started {N T : ℕ} (r : Fin N → ℝ) (h : History N T) (τ : ℕ) : Prop :=
  ∃ t : Fin T, epochOf r h t = τ

/-- `𝒯(τ)`, the periods of epoch `τ`. -/
noncomputable def epochTimes {N T : ℕ} (r : Fin N → ℝ) (h : History N T) (τ : ℕ) :
    Finset (Fin T) := by
  classical
  exact Finset.univ.filter (fun t => epochOf r h t = τ)

/-- `τ₀`, the last outer iteration (the epoch of the last period; `0` when `T = 0`). -/
noncomputable def tau0 {N T : ℕ} (r : Fin N → ℝ) (h : History N T) : ℕ :=
  Finset.univ.sup (fun t : Fin T => epochOf r h t)

/-- The state at the first period of epoch `τ` (the initial state if epoch `τ` does not start). -/
noncomputable def epochState {N T : ℕ} (r : Fin N → ℝ) (h : History N T) (τ : ℕ) : AlgState := by
  classical
  exact if hs : (epochTimes r h τ).Nonempty then stateOf r h ((epochTimes r h τ).min' hs)
    else initState

/-- `a_τ` along `h` (meaningful when epoch `τ` starts). -/
noncomputable def epochA {N T : ℕ} (r : Fin N → ℝ) (h : History N T) (τ : ℕ) : ℝ :=
  (epochState r h τ).a

/-- `b_τ` along `h` (meaningful when epoch `τ` starts). -/
noncomputable def epochB {N T : ℕ} (r : Fin N → ℝ) (h : History N T) (τ : ℕ) : ℝ :=
  (epochState r h τ).b

/-- The deterministic last epoch that can start, `τ̄(T) = max{τ : ∑_{τ' < τ} n_τ' < T}`
(`0` if no epoch can start). Every epoch `τ'` that ends before the horizon uses at least
`n_τ'` periods, so `τ₀ ≤ τ̄(T)` along every history. -/
noncomputable def tauBar (T : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun τ => ∑ τ' ∈ Finset.range τ, nEpoch T τ' < T) T

/-! ### The events `ℰ_ω(τ)` and `ψ^ω_τ(α, β)` of (14) -/

/-- The events of p. 12–13, on histories where epoch `τ` starts:
`ℰ₁(τ) : θ* < a_τ < b_τ`, `ℰ₂(τ) : a_τ ≤ θ* ≤ b_τ`, `ℰ₃(τ) : a_τ < b_τ < θ*`
(any other index gives the empty event). -/
def Event {N T : ℕ} (v r : Fin N → ℝ) (ω τ : ℕ) (h : History N T) : Prop :=
  Started r h τ ∧
    ((ω = 1 ∧ thetaStar v r < epochA r h τ ∧ epochA r h τ < epochB r h τ) ∨
     (ω = 2 ∧ epochA r h τ ≤ thetaStar v r ∧ thetaStar v r ≤ epochB r h τ) ∨
     (ω = 3 ∧ epochA r h τ < epochB r h τ ∧ epochB r h τ < thetaStar v r))

/-- The regret of outer iterations `τ, τ + 1, …, τ₀` along `h`:
`∑_{τ'=τ}^{τ₀} ∑_{t ∈ 𝒯(τ')} R(S*) − R(S_t)`. -/
noncomputable def regretToGo {N T : ℕ} (v r : Fin N → ℝ) (h : History N T) (τ : ℕ) : ℝ :=
  ∑ τ' ∈ Finset.Icc τ (tau0 r h), ∑ t ∈ epochTimes r h τ',
    (optRev v r - rev v r (offered (adaptivePolicy r T) h t))

/-- The conditioning event of (14): `ℰ_ω(τ)`, `|a_τ − θ*| = α` and `|F(a_τ) − a_τ| = β`. -/
def Cond {N T : ℕ} (v r : Fin N → ℝ) (ω τ : ℕ) (α β : ℝ) (h : History N T) : Prop :=
  Event v r ω τ h ∧ |epochA r h τ - thetaStar v r| = α ∧
    |F v r (epochA r h τ) - epochA r h τ| = β

open scoped Classical in
/-- `ψ^ω_τ(α, β)` of (14): the conditional expectation of the regret of outer iterations
`τ, …, τ₀` given `ℰ_ω(τ)`, `|a_τ − θ*| = α`, `|F(a_τ) − a_τ| = β`, under the policy
`adaptivePolicy r T` and horizon `T`. It is a ratio of finite sums over histories, and equals `0`
when the conditioning event has probability `0`. -/
noncomputable def psi {N : ℕ} (v r : Fin N → ℝ) (T ω τ : ℕ) (α β : ℝ) : ℝ :=
  (∑ h : History N T, if Cond v r ω τ α β h then
      histProb v (adaptivePolicy r T) h * regretToGo v r h τ else 0) /
    probT v (adaptivePolicy r T) T (Cond v r ω τ α β)

end MNLTrisection.Adaptive



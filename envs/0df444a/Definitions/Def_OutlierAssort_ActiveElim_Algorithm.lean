-- Prove2me | Definitions.Def_OutlierAssort_ActiveElim_Algorithm
-- name    : OutlierAssort_ActiveElim_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T08:39:17.094722+00:00
-- url     : https://prove2.me/theorems/9859f8a2-f06a-49c9-ba8b-b78acaebcb9a
-- title:
--   Algorithm 1, p. 10 — the active-elimination policy (line 14 read with min), its epoch schedule, the path law against an adaptive adversary and the TOTE regret (2)
-- statement:
--   This file encodes **Algorithm 1** of Chen, Krishnamurthy and Wang, the run of the algorithm against an adaptive adversary, and the **TOTE regret** (2).
--
--   The algorithm's inputs are the horizon $T$, an outlier proportion $\bar\varepsilon$, the revenues $r$ and the capacity $K$. It also takes a routine `sel` for the constrained argmax of line 5. `IsArgmaxSel` requires that, for every weight vector $w$, active set $A$ and item $i \in A$, the set `sel w A i` maximize $R(S;w)$ over $\{S\subseteq A : |S| \le K,\ i \in S\}$, with any tie-break.
--
--   **Epochs.** Set $T_0 = \lceil 128 (K+1)^2 N \ln T\rceil$ and $T_\tau = 2^\tau T_0$. Epoch $\tau$ occupies the periods from $\sum_{\sigma<\tau} T_\sigma$ to $\sum_{\sigma \le \tau} T_\sigma - 1$. The run stops after $T$ periods, so the last epoch $\tau_0$, the one containing period $T-1$, may be truncated.
--
--   **State.** At the start of epoch $\tau$ the algorithm holds an active set $\mathcal A^{(\tau)}$, estimates $\hat v^{(\tau)}$ and an error bound $\hat\Delta_{\bar\varepsilon}(\tau)$, starting from $\mathcal A^{(0)} = [N]$, $\hat v^{(0)} \equiv 1$ and $\hat\Delta(0) = 1$. In epoch $\tau$:
--
--   1. $S^{(i)}_\tau$ is the argmax of line 5, and $\gamma^{(\tau)} = \max_{i\in\mathcal A^{(\tau)}} R(S_\tau^{(i)}; \hat v^{(\tau)})$.
--   2. $\mathcal A^{(\tau+1)} = \{ i \in \mathcal A^{(\tau)} : R(S_\tau^{(i)}; \hat v^{(\tau)}) + 2\hat\Delta_{\bar\varepsilon}(\tau) \ge \gamma^{(\tau)}\}$.
--   3. In each period an item $i$ is drawn uniformly from $\mathcal A^{(\tau+1)}$ and $S_\tau^{(i)}$ is offered. The counter $n_i$ counts the periods in which $i$ was drawn and bought, and $n_0(i)$ the periods in which $i$ was drawn and nothing was bought.
--   4. At the end of the epoch, $\hat v^{(\tau+1)}_i = \min\{1, n_i/n_0(i)\}$ for $i \in \mathcal A^{(\tau+1)}$, and $\hat v^{(\tau+1)}_i = 1$ if $n_0(i) = 0$.
--   5. With $\bar\varepsilon_\tau = \min\{1, \bar\varepsilon T/T_\tau\}$ and $N_\tau = |\mathcal A^{(\tau+1)}|$, the new error bound is
--   $$
--   \hat\Delta_{\bar\varepsilon}(\tau+1) = \begin{cases} 1, & T_\tau < \frac{\bar\varepsilon T}{4(K+1)},\\[2pt] 16K(K+1)\Big(\frac{\bar\varepsilon_\tau}{2} + \sqrt{\frac{\bar\varepsilon_\tau N_\tau \ln T}{T_\tau}} + \frac{2N_\tau\ln T}{3T_\tau}\Big) + 16\sqrt{\frac{K N_\tau \ln T}{T_\tau}}, & \text{otherwise.}\end{cases}
--   $$
--
--   The file also defines the following:
--
--   - the bound $\Delta^*_\varepsilon(i,\tau+1)$ of (7);
--   - the corrected bound of Corollary 1, which multiplies the last term above by $\max\{1, \sqrt{K+1}/2\}$;
--   - the success event of Lemma 1 for an epoch.
--
--   **Run and regret.** A run is recorded period by period as (drawn item, customer type, purchase). Its probability is the product over periods of the following factors:
--
--   - the uniform probability of the drawn item on $\mathcal A^{(\tau+1)}$;
--   - the indicator that the type is the adversary's $\phi_t$, a function of the public past;
--   - the probability of the purchase, under the MNL model (1) on the offered set if the customer is typical and under the adversary's $Q_t$ if the customer is an outlier.
--
--   The TOTE regret (2) is
--   $$
--   \mathrm{Regret}_{\mathrm{TOTE}}(T) = \mathbb E\Big[\sum_{t} \big(R(S^*; v) - R(S_t; v)\big)\Big].
--   $$
--
--   **Formalization Note.** Line 14 is printed as $\max\{1, n_i/n_0(i)\}$, which is always at least 1, contradicting $\hat v \in [0,1]^N$ (p. 9) and the proof on ec3. It is read as $\min$. With the printed $\max$ the algorithm eliminates the optimal item on a two-item instance. Lean's $x/0 = 0$ would make $\hat v_i = 0$ when $n_0(i)=0$; the definition sets $\hat v_i = 1$ there instead. $T_0$ is rounded up to an integer. Logarithms are natural.
-- source:
--   Chen, Krishnamurthy, Wang, Robust Dynamic Assortment Optimization in the Presence of Outlier Customers, arXiv:1910.04183v2, p. 10, Algorithm 1 (lines 1–18); p. 8, (2); p. 13, (7); p. 14, Corollary 1

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model

namespace OutlierAssort.ActiveElim

/-- The inputs of Algorithm 1 (line 1, p. 10): the horizon `T`, the outlier proportion `ε̄`, the
revenues `r` and the capacity `K`; and `sel`, the routine that computes the constrained argmax of
line 5 (`sel w A i` is the assortment returned for the weights `w`, the active set `A` and the item
`i`). Every theorem quantifies over every `sel` satisfying `IsArgmaxSel`, i.e. over every tie-break. -/
structure Input (N : ℕ) where
  T : ℕ
  epsBar : ℝ
  r : Fin N → ℝ
  K : ℕ
  sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)

/-- `sel` computes line 5 of Algorithm 1 (with any tie-break): for every weight vector `w`, set `A`
and item `i ∈ A`, the set `sel w A i` maximizes `R(S; w)` over `{S ⊆ A : |S| ≤ K, i ∈ S}`. -/
def IsArgmaxSel {N : ℕ} (r : Fin N → ℝ) (K : ℕ)
    (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)) : Prop :=
  ∀ (w : Fin N → ℝ) (A : Finset (Fin N)) (i : Fin N), i ∈ A →
    sel w A i ⊆ A ∧ i ∈ sel w A i ∧ (sel w A i).card ≤ K ∧
      ∀ S : Finset (Fin N), S ⊆ A → i ∈ S → S.card ≤ K → rev r w S ≤ rev r w (sel w A i)

/-- `T₀ = ⌈128 (K + 1)² N ln T⌉` (line 3, p. 10; rounded up to an integer number of periods). -/
noncomputable def T0 (N K T : ℕ) : ℕ :=
  ⌈128 * ((K : ℝ) + 1) ^ 2 * (N : ℝ) * Real.log (T : ℝ)⌉₊

/-- The length `T_τ = 2^τ T₀` of epoch `τ` (line 8, p. 10). -/
noncomputable def epochLen (N K T τ : ℕ) : ℕ := 2 ^ τ * T0 N K T

/-- The first period of epoch `τ` (0-based): `∑_{σ < τ} T_σ`. -/
noncomputable def epochStart (N K T τ : ℕ) : ℕ := ∑ σ ∈ Finset.range τ, epochLen N K T σ

open scoped Classical in
/-- The epoch containing period `t` (0-based): the largest `τ ≤ t` with `epochStart τ ≤ t`. (When
`T₀ ≥ 1`, `epochStart τ ≥ τ`, so this is the unique `τ` with
`epochStart τ ≤ t < epochStart (τ + 1)`.) -/
noncomputable def epochOf (N K T t : ℕ) : ℕ :=
  ((Finset.range (t + 1)).filter (fun τ => epochStart N K T τ ≤ t)).sup id

/-- `τ₀`, the index of the last epoch, which contains the last period `T - 1`; it is truncated when
`epochStart (τ₀ + 1) > T`. -/
noncomputable def tau0 (N K T : ℕ) : ℕ := epochOf N K T (T - 1)

/-- The error upper bound of line 15 (p. 10) for an epoch of length `t` whose next active set has
`n` items, with outlier proportion `e`: `1` if `t < e T / (4 (K + 1))`, and otherwise
`16 K (K + 1) (e_t / 2 + √(e_t n ln T / t) + 2 n ln T / (3 t)) + 16 √(K n ln T / t)` with
`e_t = min{1, e T / t}`. Algorithm 1 uses `e = ε̄`; Corollary 1 also evaluates it at other `e`. -/
noncomputable def deltaHat (e : ℝ) (T K t n : ℕ) : ℝ :=
  if (t : ℝ) < e * T / (4 * ((K : ℝ) + 1)) then 1
  else
    16 * K * ((K : ℝ) + 1) *
        (min 1 (e * T / t) / 2 + Real.sqrt (min 1 (e * T / t) * n * Real.log T / t) +
          2 * n * Real.log T / (3 * t)) +
      16 * Real.sqrt (K * n * Real.log T / t)

/-- The corrected error bound used in Corollary 1: `deltaHat` with its last term
`16 √(K n ln T / t)` multiplied by `max{1, √(K + 1) / 2}`. -/
noncomputable def deltaHatCor (e : ℝ) (T K t n : ℕ) : ℝ :=
  if (t : ℝ) < e * T / (4 * ((K : ℝ) + 1)) then 1
  else
    16 * K * ((K : ℝ) + 1) *
        (min 1 (e * T / t) / 2 + Real.sqrt (min 1 (e * T / t) * n * Real.log T / t) +
          2 * n * Real.log T / (3 * t)) +
      max 1 (Real.sqrt ((K : ℝ) + 1) / 2) * (16 * Real.sqrt (K * n * Real.log T / t))

/-- The estimation error bound `∆*_ε(i, τ + 1)` of (7), p. 13, for an epoch of length `t` whose next
active set has `n` items, true outlier proportion `e`, `V_S = vS` (the true utility mass of the
assortment offered for item `i`) and `v_i = vi`:
`8 (K + 1) (e_t / 2 + √(e_t n ln T / t) + 2 n ln T / (3 t)) + 8 √((1 + V_S) v_i n ln T / t)`,
`e_t = min{1, e T / t}`. -/
noncomputable def deltaStar (e : ℝ) (T K t n : ℕ) (vS vi : ℝ) : ℝ :=
  8 * ((K : ℝ) + 1) *
      (min 1 (e * T / t) / 2 + Real.sqrt (min 1 (e * T / t) * n * Real.log T / t) +
        2 * n * Real.log T / (3 * t)) +
    8 * Real.sqrt ((1 + vS) * vi * n * Real.log T / t)

/-- The record of one period of a run of Algorithm 1: the item `j` sampled at line 10 (the
algorithm's internal randomness), the customer type `φ_t` (`true` = outlier) and the purchase `i_t`
(`none` = no purchase). The offered assortment is a function of the past and of `j`. -/
abbrev Rec (N : ℕ) := Fin N × Bool × Option (Fin N)

/-- The quantities of Algorithm 1 at the start of an epoch `τ`: the active set `A^{(τ)}`, the
estimates `v̂^{(τ)}` and the error bound `∆̂_ε̄(τ)`. -/
structure EpochState (N : ℕ) where
  A : Finset (Fin N)
  vhat : Fin N → ℝ
  dhat : ℝ

/-- `γ^{(τ)} = max_{i ∈ A^{(τ)}} R(S_τ^{(i)}; v̂^{(τ)})` (line 6); `0` if the active set is empty. -/
noncomputable def gammaHat {N : ℕ} (alg : Input N) (st : EpochState N) : ℝ :=
  if h : st.A.Nonempty then st.A.sup' h (fun i => rev alg.r st.vhat (alg.sel st.vhat st.A i))
  else 0

/-- `A^{(τ+1)} = {i ∈ A^{(τ)} : R(S_τ^{(i)}; v̂^{(τ)}) + 2 ∆̂_ε̄(τ) ≥ γ^{(τ)}}` (line 7). -/
noncomputable def nextActive {N : ℕ} (alg : Input N) (st : EpochState N) : Finset (Fin N) :=
  st.A.filter (fun i => gammaHat alg st ≤ rev alg.r st.vhat (alg.sel st.vhat st.A i) + 2 * st.dhat)

/-- The counter `n_i` of line 12 over the periods `a ≤ s < b` of the record `p`: the number of those
periods at which `i` was sampled and purchased. -/
noncomputable def purchCount {N t : ℕ} (p : Fin t → Rec N) (a b : ℕ) (i : Fin N) : ℕ :=
  (Finset.univ.filter (fun s : Fin t => a ≤ s.val ∧ s.val < b ∧ (p s).1 = i ∧ (p s).2.2 = some i)).card

/-- The counter `n_0(i)` of line 12 over the periods `a ≤ s < b` of the record `p`: the number of
those periods at which `i` was sampled and nothing was purchased. -/
noncomputable def noPurchCount {N t : ℕ} (p : Fin t → Rec N) (a b : ℕ) (i : Fin N) : ℕ :=
  (Finset.univ.filter (fun s : Fin t => a ≤ s.val ∧ s.val < b ∧ (p s).1 = i ∧ (p s).2.2 = none)).card

/-- The estimate of line 14, read with `min`: `v̂_i = min{1, n_i / n_0(i)}`, and `v̂_i = 1` when
`n_0(i) = 0`. -/
noncomputable def estimate (n n0 : ℕ) : ℝ :=
  if n0 = 0 then 1 else min 1 ((n : ℝ) / n0)

/-- The state of Algorithm 1 at the start of epoch `τ`, computed from the record `p` of the periods
run so far (lines 3–15). Epoch `τ` occupies the periods `epochStart τ ≤ s < epochStart τ + T_τ`.
`state 0 = (A^{(0)} = [N], v̂^{(0)} ≡ 1, ∆̂(0) = 1)`; `state (τ + 1)` has the active set `A^{(τ+1)}`
of line 7, the estimates of line 14 for `i ∈ A^{(τ+1)}` from the counters of epoch `τ` (other items
keep their old value and are never used again), and `∆̂_ε̄(τ + 1)` of line 15 with `T_τ` and
`N_τ = |A^{(τ+1)}|`. -/
noncomputable def state {N : ℕ} (alg : Input N) {t : ℕ} (p : Fin t → Rec N) : ℕ → EpochState N
  | 0 => ⟨Finset.univ, fun _ => 1, 1⟩
  | τ + 1 =>
    let st := state alg p τ
    let A' := nextActive alg st
    let a := epochStart N alg.K alg.T τ
    let b := a + epochLen N alg.K alg.T τ
    ⟨A', fun i => if i ∈ A' then estimate (purchCount p a b i) (noPurchCount p a b i) else st.vhat i,
      deltaHat alg.epsBar alg.T alg.K (epochLen N alg.K alg.T τ) A'.card⟩

/-- The success event of Lemma 1 for epoch `σ` on the record `p`: every item `i ∈ A^{(σ+1)}` has
`|v̂_i^{(σ+1)} − v_i| ≤ ∆*_ε(i, σ + 1)` of (7), where `N_σ = |A^{(σ+1)}|` and `V_S` is the true
utility mass of the assortment `S_σ^{(i)}` offered for `i` during epoch `σ`. -/
def EstimateWithin {N : ℕ} (alg : Input N) (v : Fin N → ℝ) (eps : ℝ) {t : ℕ} (p : Fin t → Rec N)
    (σ : ℕ) : Prop :=
  ∀ i ∈ (state alg p (σ + 1)).A,
    |(state alg p (σ + 1)).vhat i - v i| ≤
      deltaStar eps alg.T alg.K (epochLen N alg.K alg.T σ) (state alg p (σ + 1)).A.card
        (∑ j ∈ alg.sel (state alg p σ).vhat (state alg p σ).A i, v j) (v i)

/-- The corrected error bound of Corollary 1 at the start of epoch `τ`, for the outlier proportion
`e`: `1` for `τ = 0`, and `deltaHatCor e` with `T_σ` and `N_σ = |A^{(σ+1)}|` for `τ = σ + 1`. -/
noncomputable def deltaHatCorAt {N : ℕ} (alg : Input N) {t : ℕ} (p : Fin t → Rec N) (e : ℝ) :
    ℕ → ℝ
  | 0 => 1
  | σ + 1 => deltaHatCor e alg.T alg.K (epochLen N alg.K alg.T σ) (state alg p (σ + 1)).A.card

/-- The assortment `S_τ^{(j)}` offered at period `t` (line 11) after the record `p` of periods
`0, …, t - 1`, when item `j` was sampled: `τ` is the epoch of `t`. -/
noncomputable def offered {N : ℕ} (alg : Input N) {t : ℕ} (p : Fin t → Rec N) (j : Fin N) :
    Finset (Fin N) :=
  let st := state alg p (epochOf N alg.K alg.T t)
  alg.sel st.vhat st.A j

/-- The assortment offered at period `s` of the record `h`. -/
noncomputable def offeredAt {N t : ℕ} (alg : Input N) (h : Fin t → Rec N) (s : Fin t) :
    Finset (Fin N) :=
  offered alg (restrict h s.val s.isLt.le) (h s).1

/-- The public past (Definition 1's `F_{t-1}`) of the record `p`: the types, offered assortments and
purchases. -/
noncomputable def pubPast {N t : ℕ} (alg : Input N) (p : Fin t → Rec N) : Fin t → PubRec N :=
  fun s => ((p s).2.1, offeredAt alg p s, (p s).2.2)

/-- The probability that period `t` produces the record `x = (j, φ, i)` after the record `p` of
periods `0, …, t - 1` (Definition 1, item 3, and lines 10–11): `j` is uniform on `A^{(τ+1)}` of the
current epoch `τ`; the type is the adversary's `φ_t`, a function of the public past; the purchase is
drawn from the MNL model (1) on `S_τ^{(j)}` for a typical customer and from the adversary's `Q_t` for
an outlier. -/
noncomputable def stepProb {N : ℕ} (alg : Input N) (v : Fin N → ℝ) (adv : Adversary N) {t : ℕ}
    (p : Fin t → Rec N) (x : Rec N) : ℝ :=
  let st := state alg p (epochOf N alg.K alg.T t)
  let A' := nextActive alg st
  let S := alg.sel st.vhat st.A x.1
  let φ := adv.outlier t (pubPast alg p)
  (if x.1 ∈ A' then 1 / (A'.card : ℝ) else 0) * (if x.2.1 = φ then 1 else 0) *
    (if φ then adv.model t (pubPast alg p) S x.2.2 else mnlLaw v S x.2.2)

/-- The path law of the `T` periods of Algorithm 1 against the adversary: the probability of the
record `h` is the product of the step probabilities. -/
noncomputable def pathLaw {N : ℕ} (alg : Input N) (v : Fin N → ℝ) (adv : Adversary N)
    (h : Fin alg.T → Rec N) : ℝ :=
  ∏ t : Fin alg.T, stepProb alg v adv (restrict h t.val t.isLt.le) (h t)

open scoped Classical in
/-- The probability of an event `E` on the records of the `T` periods (a finite sum). -/
noncomputable def prob {N : ℕ} (alg : Input N) (v : Fin N → ℝ) (adv : Adversary N)
    (E : (Fin alg.T → Rec N) → Prop) : ℝ :=
  ∑ h : Fin alg.T → Rec N, if E h then pathLaw alg v adv h else 0

/-- The TOTE regret (2), p. 8: `E[∑_{t=1}^T R(S*; v) − R(S_t; v)]` under the path law. -/
noncomputable def toteRegret {N : ℕ} (alg : Input N) (v : Fin N → ℝ) (adv : Adversary N) : ℝ :=
  ∑ h : Fin alg.T → Rec N,
    pathLaw alg v adv h * ∑ t : Fin alg.T, (optRev alg.r v alg.K - rev alg.r v (offeredAt alg h t))

end OutlierAssort.ActiveElim



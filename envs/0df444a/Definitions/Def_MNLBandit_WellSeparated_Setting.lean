-- Prove2me | Definitions.Def_MNLBandit_WellSeparated_Setting
-- name    : MNLBandit_WellSeparated_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:08:21.273596+00:00
-- url     : https://prove2.me/theorems/135971ca-5f4b-40d8-bc30-c1890e096fe6
-- title:
--   §2–§3, §6.1, pp. 5–9, 19–20 — history law (2.5), Algorithm 1 along a history, Δ(v) (6.1), τ (6.2), good epochs
-- statement:
--   This module defines the policy studied in §6.1 of Agrawal, Avadhanula, Goyal and Zeevi (Algorithm 1, read along a history), together with the separation $\Delta(\mathbf v)$, the threshold $\tau$ and the "good epochs" of the well-separated analysis. It builds on the shared modules `MNLBandit.UCB.Setting` (the MNL choice probabilities (2.1), the feasible family (2.3), Assumption 4.1.2, $R(S^*,\mathbf v)$, deterministic policies, the regret (2.6) and argmax selectors), `MNLBandit.UCB.Algorithm1` (Algorithm 1 itself: epoch records, the estimates (3.1)–(3.4) and the optimistic assortment) and `MNLBandit.LowerBound.Setting` (the cardinality family $\{S:|S|\le K\}$).
--
--   **The model.** There are $N$ products. Offered an assortment $S$, a customer buys $i\in S$ with probability $v_i/(1+\sum_{j\in S}v_j)$ and nothing with probability $1/(1+\sum_{j\in S}v_j)$, where $v_1,\dots,v_N\ge0$ and $v_0=1$. With known revenues $r_i$ the expected revenue (2.2) of $S$ is
--   $$
--   R(S,\mathbf v)=\frac{\sum_{i\in S}r_iv_i}{1+\sum_{j\in S}v_j}.
--   $$
--   A deterministic nonanticipating policy chooses $S_t$ from the choices $c_1,\dots,c_{t-1}$. Given the offered sets the choices are independent, so a choice history $(c_1,\dots,c_T)$ has probability $\prod_{t=1}^Tp_{c_t}(S_t)$. This module records that law, the probability $P_T(E)$ of an event $E$ on histories of length $T$, and the expected cumulative revenue $\mathbb E_\pi\sum_{t=1}^TR(S_t,\mathbf v)$ (2.5).
--
--   **Algorithm 1.** The algorithm works in epochs. Epoch $\ell$ offers one assortment $S_\ell$ repeatedly until a customer buys nothing. For a product $i$, let $\hat v_{i,\tau}$ be the number of purchases of $i$ in epoch $\tau$ (3.1). Let $T_i(\ell)$ be the number of epochs $\tau\le\ell$ with $i\in S_\tau$ (3.2), and let $\bar v_{i,\ell}$ be the average of $\hat v_{i,\tau}$ over those epochs (3.3). At the end of epoch $\ell$ the upper confidence bound (3.4) is
--   $$
--   v^{\mathrm{UCB}}_{i,\ell}=\bar v_{i,\ell}+\sqrt{\bar v_{i,\ell}\,\frac{48\log(\sqrt N\ell+1)}{T_i(\ell)}}+\frac{48\log(\sqrt N\ell+1)}{T_i(\ell)},
--   $$
--   with $v^{\mathrm{UCB}}_{i,\ell}=1$ while $T_i(\ell)=0$. The next assortment (3.6)–(3.7) is
--   $$
--   S_{\ell+1}\in\arg\max_{S\in\mathcal S}\tilde R_{\ell+1}(S),\qquad \tilde R_{\ell+1}(S)=\frac{\sum_{i\in S}r_iv^{\mathrm{UCB}}_{i,\ell}}{1+\sum_{j\in S}v^{\mathrm{UCB}}_{j,\ell}}.
--   $$
--   Ties are broken by an arbitrary but fixed selector. The algorithm never uses $\mathbf v$. Along a history of $T$ customers, $L$ denotes the number of epochs started within the horizon.
--
--   **Separation.** The separation (6.1) of the instance is
--   $$
--   \Delta(\mathbf v)=\min_{S\in\mathcal S:\ R(S,\mathbf v)\neq R(S^*,\mathbf v)}\big(R(S^*,\mathbf v)-R(S,\mathbf v)\big),
--   $$
--   the gap between the optimal and the second-best expected revenue. With $C_1=\sqrt{72}+\sqrt{24}$ and $C_2=144$ (the constants of Lemma 4.1) and $C=\max\{C_1^2,C_2\}$, the threshold (6.2) is
--   $$
--   \tau=\frac{4NC\log NT}{\Delta^2(\mathbf v)}.
--   $$
--   Epoch $\ell$ is **good** if for every product $i$
--   $$
--   0\le v^{\mathrm{UCB}}_{i,\ell}-v_i\le C_1\sqrt{\frac{v_i\log(\sqrt N\ell+1)}{T_i(\ell)}}+C_2\frac{\log(\sqrt N\ell+1)}{T_i(\ell)}.
--   $$
--
--   These objects are the vocabulary of the instance-dependent analysis of Algorithm 1: Theorem 3 bounds its regret by a multiple of $N^2\log T/\Delta(\mathbf v)$.
--
--   **Formalization Note** Products are `Fin N` (the paper's product $i$ is index $i-1$), choices are `Option (Fin N)` with `none` the no-purchase option, and customers are 0-based. The revenue is the published `ChoiceCDLP.MNL.mnlObjective v r 1 S`. `alg1` is `MNLBandit.UCB.alg1`, a function of the observed choices through a state (completed epochs with their assortments and purchase counts, the current assortment, the current counts); `completedEpochs h` lists the completed epochs along $h$. `epochSet h ℓ` is $S_\ell$ (computed from the first $\ell-1$ completed epochs), `Tcount h i ℓ` is (3.2) literally, and `vUCB h i ℓ` is (3.4) computed from the first $\ell$ completed epochs. `epochsStarted h` is $L$, counting an epoch in progress at time $T$. Four conventions are disclosed:
--
--   1. The UCB equals $1$ while $T_i(\ell)=0$; the paper sets only $v^{\mathrm{UCB}}_{i,0}=1$ and (3.4) divides by $T_i(\ell)$.
--   2. When every feasible assortment is optimal, the minimum in (6.1) is over the empty set and `gap` is set to $1$. The regret is then $0$, so no statement changes meaning, and no junk division by $0$ occurs.
--   3. The good-epoch upper inequality is required only when $T_i(\ell)\ge1$. The page writes both inequalities; Appendix C's (C.2) prints "or", a slip for "and".
--   4. The constants $C_1,C_2$ are the values the proof of Lemma 4.1 establishes (p. 35); the paper only says they exist.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, pp. 5–9, (2.1)–(2.6), (3.1)–(3.7), Algorithm 1; p. 11, Assumption 4.1; p. 19, (6.1); p. 20, (6.2) and the good-epoch display; p. 35 (values of C₁, C₂)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_LowerBound_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1
import Definitions.Def_MNLBandit_UCB_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-! ### The MNL model, policies and the history law (§2, pp. 5–7)

Products are `Fin N` (the paper's product `i` is index `i - 1`); a choice outcome is
`Option (Fin N)`, `none` being the no-purchase alternative `0`. The no-purchase weight is
normalized to `v₀ = 1` (p. 5). The choice probabilities (2.1), the feasible family (2.3),
Assumption 4.1.2, `R(S*, v)`, policies, the regret (2.6) and argmax selectors are those of
`MNLBandit.UCB` (module `Def_MNLBandit_UCB_Setting`); the completed-epoch records are
`MNLBandit.UCB.EpochRecord`, and the cardinality family is `MNLBandit.LowerBound.cardFamily`. -/

/-- The expected revenue (2.2), p. 5: `R(S, v) = ∑_{i ∈ S} r_i v_i / (1 + ∑_{j ∈ S} v_j)`,
the published MNL objective with no-purchase weight `1`. -/
noncomputable def revenue {N : ℕ} (v r : Fin N → ℝ) (S : Finset (Fin N)) : ℝ :=
  mnlObjective v r 1 S

/-- The choices of the customers before `t` in a length-`T` history. -/
def histPrefix {N T : ℕ} (h : Fin T → Option (Fin N)) (t : Fin T) : Fin t.val → Option (Fin N) :=
  fun u => h (Fin.castLE t.isLt.le u)

/-- The law of the length-`T` choice history under policy `π`: given the offered sets the choices
are independent with the MNL probabilities (p. 5), so
`ℙ_π(h) = ∏_t p_{h_t}(S_t)` with `S_t = π_t(h_0, …, h_{t-1})`. -/
noncomputable def histProb {N : ℕ} (v : Fin N → ℝ) (π : MNLBandit.UCB.Policy N) (T : ℕ)
    (h : Fin T → Option (Fin N)) : ℝ :=
  ∏ t : Fin T, MNLBandit.UCB.choiceProb v (π t (histPrefix h t)) (h t)

/-- `P_T(E) = ∑_h ℙ_π(h) 𝟙{E h}`, the probability of an event on length-`T` histories. -/
noncomputable def probT {N : ℕ} (v : Fin N → ℝ) (π : MNLBandit.UCB.Policy N) (T : ℕ)
    (E : (Fin T → Option (Fin N)) → Prop) : ℝ := by
  classical
  exact ∑ h : Fin T → Option (Fin N), if E h then histProb v π T h else 0

/-- The cumulative expected revenue (2.5), p. 6: `𝔼_π ∑_{t=1}^T R(S_t, v)`. -/
noncomputable def expectedRevenue {N : ℕ} (v r : Fin N → ℝ) (π : MNLBandit.UCB.Policy N) (T : ℕ) : ℝ :=
  ∑ h : Fin T → Option (Fin N),
    histProb v π T h * ∑ t : Fin T, revenue v r (π t (histPrefix h t))

/-! ### Algorithm 1 (pp. 8–9)

The policy and its state machine are those of `MNLBandit.UCB` (module `Def_MNLBandit_UCB_Algorithm1`):
the upper confidence bound (3.4) is `MNLBandit.UCB.vUCBL`, the optimistic assortment (3.6)–(3.7) is
`MNLBandit.UCB.optimisticSet`, and the state after a sequence of choices is `MNLBandit.UCB.runAlg`. -/

/-- Algorithm 1 as a policy (`MNLBandit.UCB.alg1`): customer `t` is offered the assortment of the
current epoch after the choices of customers `0, …, t - 1`. It uses `N`, `r`, the tie-breaking
selector over `𝒮` and the observed choices only, never `v`. -/
noncomputable abbrev alg1 {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) :
    MNLBandit.UCB.Policy N :=
  MNLBandit.UCB.alg1 r sel

/-! ### Epochs of a history of Algorithm 1 -/

/-- The epochs completed (closed by a no-purchase) along the history `h`, oldest first, each with
its assortment `S_τ` and purchase counts `v̂_{·,τ}`. -/
noncomputable def completedEpochs {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) :
    List (MNLBandit.UCB.EpochRecord N) :=
  (MNLBandit.UCB.runAlg r sel (List.ofFn h)).past

/-- The number of epochs completed within the first `T` customers. -/
noncomputable def epochsDone {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) : ℕ :=
  (completedEpochs r sel h).length

/-- The number `L` of epochs started within the first `T` customers (p. 8): the completed ones,
plus one if the last customer made a purchase (an epoch in progress). -/
noncomputable def epochsStarted {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) : ℕ :=
  epochsDone r sel h + (match (List.ofFn h).getLast? with
    | some (some _) => 1
    | _ => 0)

/-- `S_ℓ` (1-based `ℓ ≥ 1`): the assortment Algorithm 1 offers in epoch `ℓ` along `h`, computed
from the first `ℓ - 1` completed epochs. Meaningful for `ℓ ≤ epochsDone + 1`. -/
noncomputable def epochSet {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) (ℓ : ℕ) :
    Finset (Fin N) :=
  MNLBandit.UCB.optimisticSet r sel ((completedEpochs r sel h).take (ℓ - 1))

/-- `T_i(ℓ) = |{τ ≤ ℓ | i ∈ S_τ}|` (3.2), along `h`. -/
noncomputable def Tcount {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) (i : Fin N)
    (ℓ : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 ℓ).filter (fun τ => i ∈ epochSet r sel h τ)).card

/-- `v^UCB_{i,ℓ}` (3.4) along `h`: the upper confidence bound computed at the end of epoch `ℓ`
from the first `ℓ` completed epochs (`1` while `T_i(ℓ) = 0`, in particular `v^UCB_{i,0} = 1`).
Meaningful for `ℓ ≤ epochsDone`. -/
noncomputable def vUCB {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) (i : Fin N)
    (ℓ : ℕ) : ℝ :=
  MNLBandit.UCB.vUCBL ((completedEpochs r sel h).take ℓ) i

/-! ### Well-separated instances (§6.1, pp. 19–20) -/

/-- The constant `C₁ = √72 + √24` of Lemma 4.1.2 (value established in its proof, p. 35). -/
noncomputable def C₁ : ℝ := Real.sqrt 72 + Real.sqrt 24

/-- The constant `C₂ = 144` of Lemma 4.1.2 (value established in its proof, p. 35). -/
noncomputable def C₂ : ℝ := 144

/-- The constant `C = max{C₁², C₂}` of (6.2), p. 20. -/
noncomputable def Cmax : ℝ := max (C₁ ^ 2) C₂

/-- The separation `Δ(v)` (6.1), p. 19: `min_{S ∈ 𝒮, R(S, v) ≠ R(S*, v)} (R(S*, v) − R(S, v))`.
If every feasible assortment is optimal (the minimum is over the empty set; the regret is then
`0`), the value is set to `1`. -/
noncomputable def gap {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (h𝒮 : 𝒮.Nonempty) : ℝ := by
  classical
  exact
    if hne : (𝒮.filter (fun S => revenue v r S ≠ MNLBandit.UCB.optRevenue v r 𝒮 h𝒮)).Nonempty then
      (𝒮.filter (fun S => revenue v r S ≠ MNLBandit.UCB.optRevenue v r 𝒮 h𝒮)).inf' hne
        (fun S => MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 - revenue v r S)
    else 1

/-- `τ = 4 N C log(NT) / Δ²` (6.2), p. 20. -/
noncomputable def tau (N T : ℕ) (Δ : ℝ) : ℝ :=
  4 * N * Cmax * Real.log (N * T) / Δ ^ 2

/-- Epoch `ℓ` is "good" (p. 20) along `h`: for every product `i`,
`0 ≤ v^UCB_{i,ℓ} − v_i ≤ C₁ √(v_i log(√N ℓ + 1) / T_i(ℓ)) + C₂ log(√N ℓ + 1) / T_i(ℓ)`,
the upper inequality required when `T_i(ℓ) ≥ 1`. -/
def IsGood {N T : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : Fin T → Option (Fin N)) (ℓ : ℕ) : Prop :=
  ∀ i, v i ≤ vUCB r sel h i ℓ ∧
    (1 ≤ Tcount r sel h i ℓ →
      vUCB r sel h i ℓ - v i ≤
        C₁ * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
          + C₂ * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)

end MNLBandit.WellSeparated



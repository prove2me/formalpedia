-- Prove2me | Definitions.Def_MNLBandit_UCB_Setting
-- name    : MNLBandit_UCB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:08:58.366583+00:00
-- url     : https://prove2.me/theorems/0029c214-ce8c-4934-8f0c-c387023c7c9e
-- title:
--   §2, pp. 5–7 — MNL choice probabilities (2.1), TU feasible family (2.3), history law, expected revenue (2.5) and regret (2.6)
-- statement:
--   This file sets up the **MNL-Bandit** problem of Agrawal, Avadhanula, Goyal and Zeevi.
--
--   A seller has $N$ products $1,\dots,N$ (indexed $0,\dots,N-1$ in Lean) with known revenues $r_i$. At each time $t=1,\dots,T$ the seller offers an assortment $S_t\subseteq\{1,\dots,N\}$ and observes the choice $c_t\in S_t\cup\{0\}$ of one customer, where $0$ is the no-purchase alternative. Under the **multinomial logit (MNL)** model with attraction parameters $v_1,\dots,v_N\ge 0$ and $v_0=1$,
--   $$
--   p_i(S)=\mathbb P(c_t=i\mid S_t=S)=\begin{cases}\dfrac{v_i}{1+\sum_{j\in S}v_j}, & i\in S\cup\{0\},\\[2mm] 0,&\text{otherwise.}\end{cases}
--   $$
--   The expected revenue of $S$ is $R(S,v)=\sum_{i\in S}r_iv_i/(1+\sum_{j\in S}v_j)$ (the published objective `mnlObjective v r 1 S`).
--
--   The definitions are:
--   1. `choiceProb v S`, the probabilities $p_i(S)$ (2.1) on the outcomes "no purchase" and "buy $i$".
--   2. `IsTU 𝒮`: the feasible family (2.3) is $\{S : A\,x(S)\le b\}$ for a totally unimodular integer matrix $A$ and an integer vector $b$, where $x(S)$ is the incidence vector of $S$.
--   3. `DownClosed 𝒮`: Assumption 4.1.2, $S\in\mathcal S,\ Q\subseteq S\Rightarrow Q\in\mathcal S$.
--   4. `optRevenue`: $R(S^*,v)=\max_{S\in\mathcal S}R(S,v)$ over a nonempty family.
--   5. A history of horizon $T$ is the sequence of the $T$ choices; a **policy** chooses the assortment for customer $t$ as a function of the choices of customers $1,\dots,t-1$ (2.4), and the law of the history is
--   $$
--   \mathbb P_\pi(c_1,\dots,c_T)=\prod_{t=1}^T p_{c_t}(S_t),
--   $$
--   which is the paper's conditional independence of $c_t$ given $S_t$. `probT` is the probability of an event on histories.
--   6. `expectedRevenue` is $\mathbb E_\pi\sum_{t=1}^T R(S_t,v)$ (2.5), and `regret` is
--   $$
--   \mathrm{Reg}_\pi(T,v)=T\,R(S^*,v)-\mathbb E_\pi\Big[\sum_{t=1}^T R(S_t,v)\Big]\qquad(2.6).
--   $$
--   7. `IsArgmaxSel 𝒮 sel`: `sel` returns, for every objective $f$, a member of $\mathcal S$ maximizing $f$ over $\mathcal S$. It models an arbitrary tie-breaking rule for an argmax over $\mathcal S$.
--
--   **Formalization Note.** Only deterministic policies are needed (Algorithm 1 is deterministic), so the paper's extra randomization $U$ in (2.4) is trivial and every expectation is a finite sum over the $(N+1)^T$ histories. The paper's product $i$ is `Fin N` index $i-1$; a choice is `none` (no purchase) or `some i`. The normalization $v_0=1$ is the paper's "without loss of generality" (p. 5).
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, pp. 5–7, (2.1)–(2.6); p. 11, Assumption 4.1.2

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

/-- The MNL choice probabilities (2.1) of Agrawal–Avadhanula–Goyal–Zeevi (arXiv:1706.03880v2, p. 5)
with the normalization `v₀ = 1`. Products are `Fin N` (the paper's product `i` is index `i - 1`);
an outcome is `none` (the no-purchase alternative `0`) or `some i` (a purchase of `i`). When the
assortment `S` is offered, `none` has probability `1 / (1 + ∑_{j ∈ S} v_j)`, a product `i ∈ S` has
probability `v_i / (1 + ∑_{j ∈ S} v_j)`, and a product outside `S` has probability `0`. -/
noncomputable def choiceProb {N : ℕ} (v : Fin N → ℝ) (S : Finset (Fin N)) :
    Option (Fin N) → ℝ
  | none => 1 / (1 + ∑ j ∈ S, v j)
  | some i => if i ∈ S then v i / (1 + ∑ j ∈ S, v j) else 0

/-- The feasible family (2.3), p. 6: there are a totally unimodular integer matrix `A` (with `m`
rows) and an integer vector `b` such that `S ∈ 𝒮` iff the incidence vector `x(S)` satisfies
`A x(S) ≤ b`, i.e. `∑_{i ∈ S} A_{k i} ≤ b_k` for every row `k` (the bounds `0 ≤ x ≤ 1` hold for
every incidence vector). -/
def IsTU {N : ℕ} (𝒮 : Finset (Finset (Fin N))) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) (Fin N) ℤ) (b : Fin m → ℤ), A.IsTotallyUnimodular ∧
    ∀ S : Finset (Fin N), S ∈ 𝒮 ↔ ∀ k : Fin m, ∑ i ∈ S, A k i ≤ b k

/-- Assumption 4.1.2, p. 11: `S ∈ 𝒮` and `Q ⊆ S` imply `Q ∈ 𝒮`. -/
def DownClosed {N : ℕ} (𝒮 : Finset (Finset (Fin N))) : Prop :=
  ∀ S ∈ 𝒮, ∀ Q ⊆ S, Q ∈ 𝒮

/-- The optimal expected revenue `R(S*, v) = max_{S ∈ 𝒮} R(S, v)` of (2.6), where
`R(S, v) = mnlObjective v r 1 S = ∑_{i ∈ S} r_i v_i / (1 + ∑_{j ∈ S} v_j)` is (2.2). The maximum is
over the nonempty finite family `𝒮`. -/
noncomputable def optRevenue {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (h𝒮 : 𝒮.Nonempty) : ℝ :=
  𝒮.sup' h𝒮 (fun S => mnlObjective v r 1 S)

/-- A purchase history of horizon `T`: `h t` is the choice of customer `t` (0-based, the paper's
customer `t + 1`). -/
abbrev History (N T : ℕ) := Fin T → Option (Fin N)

/-- A deterministic nonanticipating assortment policy (2.4): the assortment offered to customer `t`
is a function of the choices of customers `0, …, t - 1` (the past assortments being themselves
functions of those choices). -/
abbrev Policy (N : ℕ) := (t : ℕ) → (Fin t → Option (Fin N)) → Finset (Fin N)

/-- The choices of the customers before `t` along the history `h`. -/
def histPrefix {N T : ℕ} (h : History N T) (t : Fin T) : Fin t.val → Option (Fin N) :=
  fun u => h (Fin.castLE t.isLt.le u)

/-- The assortment `S_t` offered to customer `t` along the history `h`. -/
def offered {N T : ℕ} (π : Policy N) (h : History N T) (t : Fin T) : Finset (Fin N) :=
  π t.val (histPrefix h t)

/-- The probability of the history `h` under the policy `π` and the MNL parameters `v`: given the
offered assortment, each customer chooses according to (2.1) independently of the past (p. 5), so
`ℙ_π(h) = ∏_t p_{h_t}(S_t)`. -/
noncomputable def histProb {N T : ℕ} (v : Fin N → ℝ) (π : Policy N) (h : History N T) : ℝ :=
  ∏ t : Fin T, choiceProb v (offered π h t) (h t)

open scoped Classical in
/-- The probability `ℙ_π(E)` of an event `E` on histories of horizon `T` (a finite sum). -/
noncomputable def probT {N : ℕ} (v : Fin N → ℝ) (π : Policy N) (T : ℕ)
    (E : History N T → Prop) : ℝ :=
  ∑ h : History N T, if E h then histProb v π h else 0

/-- The cumulative expected revenue (2.5), `𝔼_π ∑_{t=1}^T R(S_t, v)`. -/
noncomputable def expectedRevenue {N : ℕ} (v r : Fin N → ℝ) (π : Policy N) (T : ℕ) : ℝ :=
  ∑ h : History N T, histProb v π h * ∑ t : Fin T, mnlObjective v r 1 (offered π h t)

/-- The regret (2.6), p. 7: `Reg_π(T, v) = T · R(S*, v) − 𝔼_π ∑_{t=1}^T R(S_t, v)`. -/
noncomputable def regret {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (h𝒮 : 𝒮.Nonempty) (π : Policy N) (T : ℕ) : ℝ :=
  (T : ℝ) * optRevenue v r 𝒮 h𝒮 - expectedRevenue v r π T

/-- `sel` is an argmax selector over `𝒮`: for every objective `f`, `sel f` is a member of `𝒮`
maximizing `f` over `𝒮`. It encodes an arbitrary tie-breaking rule for the argmax of (3.6). -/
def IsArgmaxSel {N : ℕ} (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) : Prop :=
  ∀ f : Finset (Fin N) → ℝ, sel f ∈ 𝒮 ∧ ∀ S ∈ 𝒮, f S ≤ f (sel f)

end MNLBandit.UCB



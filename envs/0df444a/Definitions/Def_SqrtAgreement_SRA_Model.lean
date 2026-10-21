-- Prove2me | Definitions.Def_SqrtAgreement_SRA_Model
-- name    : SqrtAgreement_SRA_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:03.603987+00:00
-- url     : https://prove2.me/theorems/b2dcdd8e-b891-43ae-9a36-2420eec7c350
-- title:
--   §3–§5, pp. 15–27 — multi-task elicitation game: generating model, SRA payments (Mechanism 1), expected payoff, (strict) Bayes–Nash equilibrium, CS gap δ, SRAM Γ, uninformativeness Ω
-- statement:
--   This file sets up the multi-task peer-prediction game of Kamble, Shah, Marn, Parekh and Ramchandran and the square root agreement rule (SRA).
--
--   1. **Generating model** (§3, p. 15). Entities have a type in a finite set $\mathcal X$, answers lie in a finite set $\mathcal Y$. A generating model is a pair $(P_X,\mathbf p)$: $P_X$ is a probability distribution on $\mathcal X$, and for each $x\in\mathcal X$, $\mathbf p(x)=(p_y(x);y\in\mathcal Y)$ is a probability distribution on $\mathcal Y$. There are $N$ tasks and $M$ agents; $\mathcal M_i$ is the set of agents performing task $i$ and $\mathcal N_j=\{i : j\in\mathcal M_i\}$ the set of tasks of agent $j$. The types $X_i$ of the tasks are i.i.d. with law $P_X$, and the observation $Y^i_j$ of an agent $j\in\mathcal M_i$ is drawn independently from $\mathbf p(X_i)$.
--   2. **Strategies** (p. 16). A reporting strategy $\mathbf q$ assigns to each observation $y$ a distribution $\mathbf q(y)=(q_{y'}(y);y'\in\mathcal Y)$ over reported answers. The truthful strategy is $t_{y'}(y)=\mathbf 1\{y'=y\}$; the fully informative strategy of a permutation $\sigma$ of $\mathcal Y$ reports $\sigma(y)$ after observing $y$. A strategy is *observation-independent* if $\mathbf q(y)=\mathbf q(y')$ for all $y,y'$. A profile assigns a strategy $\mathbf q^{ij}$ to each agent and task; it is *symmetric* if all agents use the same strategy on all tasks.
--   3. **SRA** (Mechanism 1, p. 18). Assume $|\mathcal M_i|\ge 2$. For each task $i\notin\mathcal N_j$ choose two distinct agents $j_1(i),j_2(i)\in\mathcal M_i$, and for each task $i\in\mathcal N_j$ a peer $j'\in\mathcal M_i$, $j'\neq j$. Given the reports $r^i_j$, with $K>0$,
--   $$\bar f_j(y)=\frac{1}{N-|\mathcal N_j|}\Big(1+\sum_{i\in\mathcal N\setminus\mathcal N_j}\mathbf 1\{r^i_{j_1(i)}=y\}\mathbf 1\{r^i_{j_2(i)}=y\}\Big),\qquad e_j(y)=\frac{K}{\sqrt{\bar f_j(y)}},$$
--   and agent $j$ is paid $\tau_j=\sum_{i\in\mathcal N_j}e_j(r^i_j)\,\mathbf 1\{r^i_j=r^i_{j'}\}$ (her peer $j'$ for task $i$).
--   4. **Expected payoff and equilibrium** (Definitions 2–3, pp. 16–17). $\mathbb E[\tau_j]$ is the expectation under the joint law of types, observations and reports induced by $(P_X,\mathbf p)$ and the profile. A profile is a Bayes–Nash equilibrium (BNE) if no agent $j$ can raise $\mathbb E[\tau_j]$ by changing her own strategies on her own tasks; it is a strict BNE if every such change that modifies at least one of her strategies on $\mathcal N_j$ strictly lowers $\mathbb E[\tau_j]$.
--   5. **Separation** (Definitions 4–5, p. 23). With $g(y)=\sum_x P_X(x)p_y(x)^2$,
--   $$\delta(P_X,\mathbf p)=\min_{y\neq y'}\Big(\sqrt{g(y)\,g(y')}-\sum_{x}P_X(x)p_y(x)p_{y'}(x)\Big),$$
--   and the model is $\alpha$-separated if $\delta(P_X,\mathbf p)\ge\alpha$.
--   6. **SRAM and uninformativeness** (Definitions 6–7, pp. 26–27). $\Gamma(Y_1,Y_2)=\sum_y\sqrt{g(y)}$. Applying $\mathbf q$ to an observation gives the garbled model with $(\mathbf p\circ\mathbf q)_y(x)=\sum_{y'}p_{y'}(x)q_y(y')$. Finally
--   $$\Omega(\mathbf q)=\frac{1}{|\mathcal Y|(|\mathcal Y|-1)}\sum_{y\in\mathcal Y}\sum_{y'\neq y''}\sqrt{q_y(y')\,q_y(y'')}.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathcal X=$ `Fin m`, $\mathcal Y=$ `Fin k`, tasks `Fin N`, agents `Fin M`; all values are real. `q obs ans` is $q_{ans}(obs)$. Every (task, agent) pair carries an observation and a report, also when $j\notin\mathcal M_i$; under a legal `Setting` no payment reads those entries, and they marginalize out when the model and the strategies are stochastic. The expectation `expPay` is the explicit finite sum of the product weight times $\tau_j$ over all types, observations and reports. Deviations of agent $j$ change only her own strategies on $\mathcal N_j$ and must be stochastic. $\bar f_j$ divides by $N-|\mathcal N_j|$ in $\mathbb R$ (junk value $0$ when $N=|\mathcal N_j|$, which the theorems exclude by taking $N$ large). `delta` is $0$ when $|\mathcal Y|<2$ (no pairs), and the prefactor of $\Omega$ is junk at $|\mathcal Y|\le 1$. "Commonly known" carries no formal content beyond taking expectations under the true model.
-- source:
--   Kamble, Shah, Marn, Parekh & Ramchandran, The Square Root Agreement Rule for Incentivizing Truthful Feedback on Online Platforms, arXiv:1507.07045v5, pp. 15–27, §3, Definitions 1–3, Mechanism 1 (eqs. (2)–(3)), Definitions 4–7 (eq. (18))

import Mathlib

namespace SqrtAgreement.SRA

open Finset

/-- Generating model `(P_X, p)` on types `Fin m` and answers `Fin k` (§3, p. 15).
`PX x` is the prior probability of type `x`; `p x y` is `p_y(x)`, the probability of
observing `y` on a task whose entity has type `x`. -/
structure GenModel (m k : ℕ) where
  PX : Fin m → ℝ
  p : Fin m → Fin k → ℝ

/-- `P_X` and every `p(x)` are probability vectors. -/
def GenModel.Valid {m k : ℕ} (G : GenModel m k) : Prop :=
  (∀ x, 0 ≤ G.PX x) ∧ (∑ x, G.PX x = 1) ∧ (∀ x y, 0 ≤ G.p x y) ∧ (∀ x, ∑ y, G.p x y = 1)

/-- `g(y) = Σ_x P_X(x) p_y(x)²`, the probability that two agents on the same task both
observe `y` (proof of Theorem 1, p. 48). -/
def GenModel.agree {m k : ℕ} (G : GenModel m k) (y : Fin k) : ℝ :=
  ∑ x, G.PX x * G.p x y ^ 2

/-- The Cauchy–Schwarz gap of the pair `(y, y')`, the expression minimized in Definition 4. -/
noncomputable def GenModel.csGap {m k : ℕ} (G : GenModel m k) (y y' : Fin k) : ℝ :=
  Real.sqrt (G.agree y * G.agree y') - ∑ x, G.PX x * G.p x y * G.p x y'

/-- Definition 4: `δ(P_X, p)`, the minimum of the Cauchy–Schwarz gap over pairs `y ≠ y'`.
Junk value `0` when there is no such pair (`k < 2`). -/
noncomputable def GenModel.delta {m k : ℕ} (G : GenModel m k) : ℝ :=
  if h : ((Finset.univ : Finset (Fin k)).offDiag).Nonempty then
    ((Finset.univ : Finset (Fin k)).offDiag).inf' h (fun yy => G.csGap yy.1 yy.2)
  else 0

/-- Definition 5: the model is `α`-separated when `δ(P_X, p) ≥ α`. -/
def GenModel.AlphaSeparated {m k : ℕ} (α : ℝ) (G : GenModel m k) : Prop :=
  α ≤ G.delta

/-- A reporting strategy on one task: `q obs ans` is the probability `q_{ans}(obs)` of
reporting `ans` after observing `obs` (§3, p. 16). -/
abbrev Strat (k : ℕ) := Fin k → Fin k → ℝ

/-- Each row `q(obs)` is a probability vector. -/
def Stoch {k : ℕ} (q : Strat k) : Prop :=
  (∀ a b, 0 ≤ q a b) ∧ ∀ a, ∑ b, q a b = 1

/-- The truthful strategy `t_{y'}(y) = 1{y' = y}` (Definition 3). -/
def truthful (k : ℕ) : Strat k := fun a b => if b = a then 1 else 0

/-- The fully informative strategy that relabels every observation `a` as `σ a`. -/
def permStrat {k : ℕ} (σ : Equiv.Perm (Fin k)) : Strat k :=
  fun a b => if b = σ a then 1 else 0

/-- The reported response is independent of the true response (Theorem 1). -/
def ObsIndependent {k : ℕ} (q : Strat k) : Prop :=
  ∀ a a' b, q a b = q a' b

/-- The population, the allocation of tasks, and the free choices of Mechanism 1, for `N`
tasks and `M` agents. `alloc i` is `M_i`; `peer j i` is `j`'s peer on a task `i ∈ N_j`;
`j1 j i`, `j2 j i` are the two agents whose reports on a task `i ∉ N_j` enter `f̄_j`. -/
structure Setting (N M : ℕ) where
  alloc : Fin N → Finset (Fin M)
  peer : Fin M → Fin N → Fin M
  j1 : Fin M → Fin N → Fin M
  j2 : Fin M → Fin N → Fin M

/-- `N_j`, the set of tasks agent `j` performs. -/
def Setting.tasks {N M : ℕ} (S : Setting N M) (j : Fin M) : Finset (Fin N) :=
  Finset.univ.filter (fun i => j ∈ S.alloc i)

/-- `|M_i| ≥ 2` for every task, and the choices of Mechanism 1 are legal: the peer is
another agent performing the task, and `j1(i) ≠ j2(i)` both perform task `i`. -/
def Setting.Legal {N M : ℕ} (S : Setting N M) : Prop :=
  (∀ i, 2 ≤ (S.alloc i).card) ∧
  (∀ j i, i ∈ S.tasks j → S.peer j i ∈ S.alloc i ∧ S.peer j i ≠ j) ∧
  (∀ j i, i ∉ S.tasks j → S.j1 j i ∈ S.alloc i ∧ S.j2 j i ∈ S.alloc i ∧ S.j1 j i ≠ S.j2 j i)

/-- A legal setting in which every agent performs at most `n` tasks (`|N_j| ≤ n`). -/
def Setting.Valid {N M : ℕ} (S : Setting N M) (n : ℕ) : Prop :=
  S.Legal ∧ ∀ j, (S.tasks j).card ≤ n

/-- Reports `r i j` of every (task, agent) pair. Entries of pairs with `j ∉ M_i` exist,
but no payment of a legal setting reads them. -/
abbrev Reports (N M k : ℕ) := Fin N → Fin M → Fin k

/-- Equation (2): `f̄_j(y) = (1/(N − |N_j|)) (1 + Σ_{i ∉ N_j} 1{r^i_{j1(i)} = y} 1{r^i_{j2(i)} = y})`,
computed in `ℝ`. -/
noncomputable def fbar {N M k : ℕ} (S : Setting N M) (r : Reports N M k) (j : Fin M)
    (y : Fin k) : ℝ :=
  (1 / ((N : ℝ) - ((S.tasks j).card : ℝ))) *
    (1 + ∑ i ∈ Finset.univ \ S.tasks j,
      (if r i (S.j1 j i) = y ∧ r i (S.j2 j i) = y then (1 : ℝ) else 0))

/-- Equation (3): `e_j(y) = K / √(f̄_j(y))`. -/
noncomputable def e {N M k : ℕ} (K : ℝ) (S : Setting N M) (r : Reports N M k) (j : Fin M)
    (y : Fin k) : ℝ :=
  K / Real.sqrt (fbar S r j y)

/-- Agent `j`'s SRA payment `τ_j` (Definition 1, Mechanism 1): on each task `i ∈ N_j`,
`e_j(y)` if `j` and her peer both report `y`, and `0` otherwise. -/
noncomputable def tau {N M k : ℕ} (K : ℝ) (S : Setting N M) (r : Reports N M k) (j : Fin M) :
    ℝ :=
  ∑ i ∈ S.tasks j, if r i j = r i (S.peer j i) then e K S r j (r i j) else 0

/-- A strategy profile: one reporting strategy per (task, agent) pair. -/
abbrev Profile (N M k : ℕ) := Fin N → Fin M → Strat k

/-- Probability of the outcome (types `x`, observations `y`, reports `r`) under the
product law of §3: types i.i.d. from `P_X`, observations independently from `p(x_i)`,
reports independently from the strategies applied to the observations. -/
noncomputable def weight {m k N M : ℕ} (G : GenModel m k) (Q : Profile N M k)
    (x : Fin N → Fin m) (y : Fin N → Fin M → Fin k) (r : Reports N M k) : ℝ :=
  (∏ i, G.PX (x i)) * (∏ i, ∏ j, G.p (x i) (y i j)) * (∏ i, ∏ j, Q i j (y i j) (r i j))

/-- `E[τ_j]` under the profile `Q`: the finite sum over the outcome space. -/
noncomputable def expPay {m k N M : ℕ} (G : GenModel m k) (K : ℝ) (S : Setting N M)
    (Q : Profile N M k) (j : Fin M) : ℝ :=
  ∑ x, ∑ y, ∑ r, weight G Q x y r * tau K S r j

/-- `E[e_j(y)]` under the profile `Q`. -/
noncomputable def expE {m k N M : ℕ} (G : GenModel m k) (K : ℝ) (S : Setting N M)
    (Q : Profile N M k) (j : Fin M) (yy : Fin k) : ℝ :=
  ∑ x, ∑ y, ∑ r, weight G Q x y r * e K S r j yy

/-- Every strategy of the profile is stochastic. -/
def ProfileStoch {N M k : ℕ} (Q : Profile N M k) : Prop :=
  ∀ i j, Stoch (Q i j)

/-- `Q'` is a unilateral deviation of agent `j` from `Q`: a profile of stochastic
strategies that agrees with `Q` for every other agent and on every task `j` does not perform. -/
def IsDeviation {N M k : ℕ} (S : Setting N M) (Q Q' : Profile N M k) (j : Fin M) : Prop :=
  ProfileStoch Q' ∧ (∀ i j', j' ≠ j → Q' i j' = Q i j') ∧ (∀ i, i ∉ S.tasks j → Q' i j = Q i j)

/-- Definition 2: `Q` is a Bayes–Nash equilibrium of the game induced by SRA. -/
def IsBNE {m k N M : ℕ} (G : GenModel m k) (K : ℝ) (S : Setting N M) (Q : Profile N M k) :
    Prop :=
  ∀ (j : Fin M) (Q' : Profile N M k), IsDeviation S Q Q' j →
    expPay G K S Q' j ≤ expPay G K S Q j

/-- Definition 2 (strict): every deviation that changes some strategy of `j` on a task of
`N_j` strictly lowers her expected payment. -/
def IsStrictBNE {m k N M : ℕ} (G : GenModel m k) (K : ℝ) (S : Setting N M)
    (Q : Profile N M k) : Prop :=
  ∀ (j : Fin M) (Q' : Profile N M k), IsDeviation S Q Q' j →
    (∃ i ∈ S.tasks j, Q' i j ≠ Q i j) → expPay G K S Q' j < expPay G K S Q j

/-- The symmetric profile in which every agent uses `q` on every task. -/
def symm {N M k : ℕ} (q : Strat k) : Profile N M k := fun _ _ => q

/-- Definition 6: the square root agreement measure `Γ(Y1, Y2) = Σ_y √(Σ_x P_X(x) p_y(x)²)`. -/
noncomputable def GenModel.sram {m k : ℕ} (G : GenModel m k) : ℝ :=
  ∑ y, Real.sqrt (G.agree y)

/-- The model of the reported responses when the strategy `q` is applied to an observation:
`(p ∘ q)_y(x) = Σ_{y'} p_{y'}(x) q_y(y')`. -/
def GenModel.garble {m k : ℕ} (G : GenModel m k) (q : Strat k) : GenModel m k :=
  ⟨G.PX, fun x y => ∑ y', G.p x y' * q y' y⟩

/-- Definition 7, (18): `Ω(q) = (1/(|Y|(|Y|−1))) Σ_y Σ_{y' ≠ y''} √(q_y(y') q_y(y''))`.
Junk prefactor at `k ≤ 1`. -/
noncomputable def uninf {k : ℕ} (q : Strat k) : ℝ :=
  (1 / ((k : ℝ) * ((k : ℝ) - 1))) *
    ∑ y, ∑ y', ∑ y'', if y' ≠ y'' then Real.sqrt (q y' y * q y'' y) else 0

end SqrtAgreement.SRA



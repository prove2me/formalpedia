-- Prove2me | Definitions.Def_BudgetFeasSubmod_Main_Model
-- name    : BudgetFeasSubmod_Main_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:22.5611+00:00
-- url     : https://prove2.me/theorems/fec8a8c4-f355-455e-b299-32333c5e46be
-- title:
--   §2–§3, pp. 5–8 — budgeted procurement instances, threshold-payment mechanisms, Simultaneous Greedy, Sample-then-Greedy and GenSm-Main
-- statement:
--   This file sets up the budgeted procurement model of Amanatidis, Kleer and Schäfer and the randomized mechanism GenSm-Main whose properties are the subject of the mission.
--
--   **Instances** (§2, pp. 5–6). A finite set $A$ of agents is given; agent $i$ has a private cost $c_i$. The auctioneer has a budget $B>0$ and a valuation $v:2^A\to\mathbb R$ that is normalized ($v(\emptyset)=0$), non-negative and submodular in the lattice form $v(S\cup T)+v(S\cap T)\le v(S)+v(T)$. The marginal value of $i$ with respect to $S$ is $v(i\mid S)=v(S\cup\{i\})-v(S)$. For $X\subseteq A$,
--   $$
--   \mathrm{opt}(X,B)=\max\Big\{v(T) : T\subseteq X,\ \sum_{i\in T}c_i\le B\Big\},\qquad \mathrm{opt}(X,\infty)=\max\{v(T) : T\subseteq X\}.
--   $$
--   Cost vectors take values in $[0,B]^A$ (Remark 2.5).
--
--   **Mechanisms** (§2, p. 6). A deterministic outcome rule $f$ maps a vector $b$ of declared costs to a set $f(b)\subseteq A$ of winners. It is *monotone* if a winner who lowers its bid remains a winner. Payments are always Myerson's threshold payments: a winner $i$ is paid
--   $$
--   p_i(b)=\sup\{t\in[b_i,B] : i\in f(t,b_{-i})\},
--   $$
--   and a loser is paid $0$. Agent $i$ with true cost $c_i$ has utility $p_i(b)-c_i$ if it wins and $p_i(b)=0$ if it loses. The mechanism is *truthful* if for every true cost vector $c\in[0,B]^A$, every agent $i$ and every misreport $t\in[0,B]$, the utility of $i$ under $c$ is at least its utility under $(t,c_{-i})$; *individually rational* if every payment is non-negative and every winner is paid at least its bid; *budget-feasible* if the payments sum to at most $B$ for every $b\in[0,B]^A$ (Definition 2.3).
--
--   **Subroutines.** A tie-breaking rule sees only the set $U$ of active agents and the two partial solutions $S_1,S_2$; whenever some $v(i\mid S_j)$, $i\in U$, is positive it returns a pair $(\hat\imath,\hat\jmath)$ with $\hat\imath\in U$ maximizing $v(i\mid S_j)$ over $U\times\{1,2\}$ (Remark 2.6). $\mathrm{alg}_2$ maps a set $S$ to a subset $T\subseteq S$ with $\mathrm{opt}(S,\infty)\le 2v(T)$. $\mathrm{alg}_1$ maps $(X,c)$, for every cost vector $c\in[0,B]^A$, to a subset $T\subseteq X$ with $\sum_{i\in T}c_i\le B$ and $\mathrm{opt}(X,B)\le e\cdot v(T)$; it is *cost-local* if it reads only the costs of the agents in $X$.
--
--   **Simultaneous Greedy$(D,v,c_D,B,x)$** (p. 8), with parameter $\beta>0$. Start with $S_1=S_2=\emptyset$, $B_1=B_2=B$, $U=D$. While $\max_{i\in U,j\in\{1,2\}}v(i\mid S_j)>0$: let $(\hat\imath,\hat\jmath)$ be the tie-breaking choice, compute the posted price $\pi=\frac{\beta B}{x}v(\hat\imath\mid S_{\hat\jmath})$; if $c_{\hat\imath}\le\pi\le B_{\hat\jmath}$, add $\hat\imath$ to $S_{\hat\jmath}$ and lower $B_{\hat\jmath}$ by $\pi$; in any case remove $\hat\imath$ from $U$. Finally return the best of $S_1,S_2,T_1=\mathrm{alg}_2(S_1),T_2=\mathrm{alg}_2(S_2)$.
--
--   **Sample-then-Greedy** puts each agent in $A_1$ or $A_2=A\setminus A_1$ with probability $1/2$, sets $x=v(\mathrm{alg}_1(A_1))$ and runs Simultaneous Greedy on $A_2$ with parameter $\beta$ (GenSm-Main uses $\beta=9.185$). **GenSm-Main** returns $\{i^*\}$, $i^*\in\arg\max_{i\in A}v(i)$, with probability $p=0.201$, and runs Sample-then-Greedy with probability $1-p$. Its randomness is the finite family of outcomes "singleton" (probability $p$) and "first half $A_1$" (probability $(1-p)/2^{|A|}$ for each $A_1\subseteq A$), and $\mathbb E(v(S))$ is the corresponding weighted sum.
--
--   These objects are shared by every statement of the mission: the goal and all milestones are statements about the outcome rules defined here and their threshold payments.
--
--   **Formalization Note** Agents form a finite type with decidable equality; values and costs are real (the paper's codomain is $\mathbb Q_{\ge0}$). Submodularity is the published `NonmonotoneSubmod.Shared.Submodular`. `opt` is a `Finset.sup'` over the budget-feasible subsets, a family that contains $\emptyset$ whenever $B\ge0$ (the fallback value $0$ for $B<0$ is never used). The threshold payment is a real `sSup` over $\{t\in[b_i,B] : i \text{ wins at } (t,b_{-i})\}$, which for a winner contains $b_i$ and is bounded by $B$. Bids are truncated to $[0,B]$ by Remark 2.5, which also replaces the printed $[c_i,\infty)$ of Lemma 2.4 by $[b_i,B]$. The price $\frac{\beta B}{x}v(\hat\imath\mid S_{\hat\jmath})$ is computed once, before the insertion (line 6 read with the pre-insertion set, as in the proof of Lemma 3.4); at $x=0$ Lean's $x^{-1}=0$ makes it $0$. The while loop is run $|D|$ times, which suffices because each iteration that passes the test removes one agent from $U\subseteq D$ and a failing test leaves the state unchanged. Line 10 returns the first maximizer in the order $S_1,S_2,T_1,T_2$, and $i^*$ is a fixed maximizer chosen without looking at costs. $\beta=9185/1000$ and $p=201/1000$ exactly. A loser's utility is $0$; the printed $p_i(b)-c_i$ is the winner's.
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, pp. 5–8, §2 (Definitions 2.1(ii), 2.3, Lemma 2.4, Remarks 2.5, 2.6) and §3 (Simultaneous Greedy, Sample-then-Greedy, GenSm-Main, p. 8)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace BudgetFeasSubmod.Main

open Finset NonmonotoneSubmod.Shared

variable {A : Type} [Fintype A] [DecidableEq A]

/-! ### Instance (§2, pp. 5–6) -/

/-- The marginal value `v(i | S) = v(S ∪ {i}) − v(S)` (§2, p. 5). -/
def marg (v : Finset A → ℝ) (i : A) (S : Finset A) : ℝ := v (insert i S) - v S

/-- Standing assumptions on the valuation (§2, p. 5): normalized, non-negative, submodular
(Definition 2.1(ii)). -/
def IsValuation (v : Finset A → ℝ) : Prop :=
  v ∅ = 0 ∧ (∀ S, 0 ≤ v S) ∧ Submodular v

/-- Cost (bid) vectors with every entry in `[0, B]` (Remark 2.5, p. 7). -/
def InDomain (B : ℝ) (b : A → ℝ) : Prop := ∀ i, 0 ≤ b i ∧ b i ≤ B

/-- `opt(X, B)`: the largest value `v(T)` over `T ⊆ X` with `∑_{i ∈ T} c_i ≤ B` (§2, p. 6).
The feasible family contains `∅` whenever `0 ≤ B`; the `else` branch (`B < 0`) is never used. -/
noncomputable def opt (v : Finset A → ℝ) (c : A → ℝ) (B : ℝ) (X : Finset A) : ℝ :=
  if h : (X.powerset.filter (fun T => ∑ i ∈ T, c i ≤ B)).Nonempty then
    (X.powerset.filter (fun T => ∑ i ∈ T, c i ≤ B)).sup' h v
  else 0

/-- `opt(X, ∞)`: the largest value `v(T)` over all `T ⊆ X` (§2, p. 6). -/
noncomputable def optInf (v : Finset A → ℝ) (X : Finset A) : ℝ :=
  X.powerset.sup' ⟨∅, Finset.empty_mem_powerset X⟩ v

/-! ### Mechanisms (§2, pp. 6–7) -/

/-- Myerson's threshold payment (Lemma 2.4, p. 6) of the deterministic outcome rule `f` at the
declaration `b`, with bids truncated to `[0, B]` (Remark 2.5): a winner `i` is paid the supremum
of the bids `t ∈ [b_i, B]` with which it still wins; a loser is paid `0`. -/
noncomputable def thr (f : (A → ℝ) → Finset A) (B : ℝ) (b : A → ℝ) (i : A) : ℝ :=
  if i ∈ f b then sSup {t : ℝ | t ∈ Set.Icc (b i) B ∧ i ∈ f (Function.update b i t)} else 0

/-- Utility of agent `i` with true costs `c` when the declaration is `b`: its payment, minus its
true cost if it is selected. -/
noncomputable def utility (f : (A → ℝ) → Finset A) (B : ℝ) (b c : A → ℝ) (i : A) : ℝ :=
  thr f B b i - (if i ∈ f b then c i else 0)

/-- Truthfulness (Definition 2.3, p. 6) with threshold payments: for every true cost vector
`c ∈ [0, B]^A`, every agent `i` and every misreport `t ∈ [0, B]`, reporting `c_i` is at least as
good as reporting `t`. -/
def IsTruthful (f : (A → ℝ) → Finset A) (B : ℝ) : Prop :=
  ∀ (c : A → ℝ) (t : ℝ) (i : A), InDomain B c → 0 ≤ t → t ≤ B →
    utility f B (Function.update c i t) c i ≤ utility f B c c i

/-- Individual rationality (Definition 2.3, p. 6) with threshold payments. -/
def IsIR (f : (A → ℝ) → Finset A) (B : ℝ) : Prop :=
  ∀ b : A → ℝ, InDomain B b → ∀ i, 0 ≤ thr f B b i ∧ (i ∈ f b → b i ≤ thr f B b i)

/-- Budget feasibility (Definition 2.3, p. 6) with threshold payments. -/
def IsBudgetFeasible (f : (A → ℝ) → Finset A) (B : ℝ) : Prop :=
  ∀ b : A → ℝ, InDomain B b → ∑ i, thr f B b i ≤ B

/-- Monotone outcome rule (§2, p. 6): a winner who lowers its bid remains a winner. -/
def IsMonotoneRule (f : (A → ℝ) → Finset A) (B : ℝ) : Prop :=
  ∀ (b : A → ℝ) (i : A) (t : ℝ), InDomain B b → 0 ≤ t → t ≤ b i → i ∈ f b →
    i ∈ f (Function.update b i t)

/-! ### Subroutine and tie-breaking specifications (pp. 7–8, 12) -/

/-- A cost-independent tie-breaking rule for line 3 of Simultaneous Greedy (Remark 2.6, p. 7):
it sees only the active set `U` and the two partial solutions `S 0, S 1`, and whenever some
`v(i | S_j)` with `i ∈ U` is positive it returns a pair `(î, ĵ)` with `î ∈ U` maximizing
`v(i | S_j)` over `U × {1, 2}`. -/
def IsArgmaxRule (v : Finset A → ℝ) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) : Prop :=
  ∀ (U : Finset A) (S : Fin 2 → Finset A), (∃ i ∈ U, ∃ j : Fin 2, 0 < marg v i (S j)) →
    (tb U S).1 ∈ U ∧ ∀ i ∈ U, ∀ j : Fin 2, marg v i (S j) ≤ marg v (tb U S).1 (S (tb U S).2)

/-- `alg2` (line 9, p. 8): a 2-approximation for unconstrained maximization, `T ⊆ S` and
`opt(S, ∞) ≤ 2 v(T)`; it sees the set only, never costs. -/
def IsUnconstrainedTwoApprox (v : Finset A → ℝ) (alg2 : Finset A → Finset A) : Prop :=
  ∀ S : Finset A, alg2 S ⊆ S ∧ optInf v S ≤ 2 * v (alg2 S)

/-- `alg1` (line 2 of Sample-then-Greedy, p. 8; proof of Lemma 3.8, p. 12): a deterministic
e-approximation for the knapsack-constrained problem: on every cost vector `c ∈ [0, B]^A` it returns
a budget-feasible subset `T` of `X` with `opt(X, B) ≤ e · v(T)`. -/
def IsKnapsackEApprox (v : Finset A → ℝ) (B : ℝ) (alg1 : Finset A → (A → ℝ) → Finset A) :
    Prop :=
  ∀ (X : Finset A) (c : A → ℝ), InDomain B c →
    alg1 X c ⊆ X ∧ ∑ i ∈ alg1 X c, c i ≤ B ∧ opt v c B X ≤ Real.exp 1 * v (alg1 X c)

/-- `alg1` reads only the costs of the agents it is run on (`alg1(A₁, v, c_{A₁}, B)`, p. 8). -/
def IsCostLocal (alg1 : Finset A → (A → ℝ) → Finset A) : Prop :=
  ∀ (X : Finset A) (c c' : A → ℝ), (∀ i ∈ X, c i = c' i) → alg1 X c = alg1 X c'

/-! ### Constants (pp. 8, 13) -/

/-- `β = 9.185` (p. 8 and proof of Corollary 3.9, p. 13). -/
noncomputable def beta : ℝ := 9185 / 1000

/-- `p = 0.201` (GenSm-Main, p. 8). -/
noncomputable def pcoin : ℝ := 201 / 1000

/-! ### Simultaneous Greedy (p. 8) -/

/-- State of Simultaneous Greedy: the two partial solutions `S 0, S 1` (the paper's `S₁, S₂`),
their remaining budgets `Bud 0, Bud 1` (`B₁, B₂`) and the active set `U`. -/
structure SGState (A : Type) where
  S : Fin 2 → Finset A
  Bud : Fin 2 → ℝ
  U : Finset A

/-- Line 1: `S₁ = S₂ = ∅`, `B₁ = B₂ = B`, `U = D`. -/
def sgInit (D : Finset A) (B : ℝ) : SGState A := ⟨fun _ => ∅, fun _ => B, D⟩

/-- The posted price `(βB/x) · v(i | S)` of lines 4 and 6 (with Lean's `x⁻¹ = 0` at `x = 0`). -/
noncomputable def price (v : Finset A → ℝ) (β B x : ℝ) (i : A) (S : Finset A) : ℝ :=
  β * B / x * marg v i S

/-- One iteration of the while loop (lines 2–7) under the declared costs `b`. If the while test
`max_{i ∈ U, j} v(i | S_j) > 0` fails the state is unchanged. Otherwise `(î, ĵ)` is chosen by `tb`,
the price `π = (βB/x) v(î | S_ĵ)` is computed once (before the insertion), `î` joins `S_ĵ` and
`B_ĵ` drops by `π` if `b_î ≤ π ≤ B_ĵ`, and `î` leaves `U`. -/
noncomputable def sgStep (v : Finset A → ℝ) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2)
    (β B x : ℝ) (b : A → ℝ) (st : SGState A) : SGState A :=
  if ∃ i ∈ st.U, ∃ j : Fin 2, 0 < marg v i (st.S j) then
    let i := (tb st.U st.S).1
    let j := (tb st.U st.S).2
    let π := price v β B x i (st.S j)
    if b i ≤ π ∧ π ≤ st.Bud j then
      ⟨Function.update st.S j (insert i (st.S j)), Function.update st.Bud j (st.Bud j - π),
        st.U.erase i⟩
    else ⟨st.S, st.Bud, st.U.erase i⟩
  else st

/-- The state at the end of the while loop: `|D|` iterations suffice, since each iteration that
passes the while test removes one agent from `U ⊆ D`, and a failing test is a fixed point. -/
noncomputable def sgRun (v : Finset A → ℝ) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2)
    (β B x : ℝ) (D : Finset A) (b : A → ℝ) : SGState A :=
  (sgStep v tb β B x b)^[D.card] (sgInit D B)

/-- The better of two sets under `v`, keeping the first one on ties. -/
noncomputable def better (v : Finset A → ℝ) (X Y : Finset A) : Finset A :=
  if v X < v Y then Y else X

/-- `Simultaneous Greedy(D, v, c_D, B, x)` with parameter `β` (p. 8), as an outcome rule of the
declared costs `b`: lines 8–11 return the first set of largest value in the order
`S₁, S₂, T₁ = alg2(S₁), T₂ = alg2(S₂)`. -/
noncomputable def simGreedy (v : Finset A → ℝ) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (β B x : ℝ) (D : Finset A)
    (b : A → ℝ) : Finset A :=
  let st := sgRun v tb β B x D b
  better v (better v (better v (st.S 0) (st.S 1)) (alg2 (st.S 0))) (alg2 (st.S 1))

/-! ### Sample-then-Greedy and GenSm-Main (p. 8) -/

/-- `Sample-then-Greedy(A, v, c, B)` once line 1 has drawn the first half `A₁`:
`x = v(alg1(A₁))`, then Simultaneous Greedy with parameter `β` on `A₂ = A ∖ A₁`
(GenSm-Main uses `β = 9.185`). -/
noncomputable def sampleThenGreedy (v : Finset A → ℝ) (alg1 : Finset A → (A → ℝ) → Finset A)
    (alg2 : Finset A → Finset A) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (β B : ℝ)
    (A₁ : Finset A) (b : A → ℝ) : Finset A :=
  simGreedy v alg2 tb β B (v (alg1 A₁ b)) (univ \ A₁) b

/-- `i* ∈ arg max_{i ∈ A} v(i)`: a fixed maximizer, independent of the costs. -/
noncomputable def istar [Nonempty A] (v : Finset A → ℝ) : A :=
  Classical.choose (Finset.exists_max_image univ (fun i => v {i}) univ_nonempty)

/-- GenSm-Main (p. 8) as the family of deterministic outcome rules indexed by its randomness:
`none` is line 1 (return `{i*}`), `some A₁` is line 2 with `A₁` the first half drawn by
Sample-then-Greedy, run with `β = 9.185`. -/
noncomputable def genSmMain [Nonempty A] (v : Finset A → ℝ)
    (alg1 : Finset A → (A → ℝ) → Finset A) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (B : ℝ) :
    Option (Finset A) → (A → ℝ) → Finset A
  | none => fun _ => {istar v}
  | some A₁ => sampleThenGreedy v alg1 alg2 tb beta B A₁

/-- Probability of each realization of GenSm-Main's randomness: `p` for `none`, and
`(1 − p)/2^n` for each of the `2^n` equally likely halvings `A₁`. -/
noncomputable def weight (ω : Option (Finset A)) : ℝ :=
  match ω with
  | none => pcoin
  | some _ => (1 - pcoin) / 2 ^ Fintype.card A

/-- `E(v(S))` for the set `S` returned by GenSm-Main(A, v, c, B). -/
noncomputable def expectedValue [Nonempty A] (v : Finset A → ℝ)
    (alg1 : Finset A → (A → ℝ) → Finset A) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (B : ℝ) (c : A → ℝ) : ℝ :=
  ∑ ω : Option (Finset A), weight ω * v (genSmMain v alg1 alg2 tb B ω c)

end BudgetFeasSubmod.Main



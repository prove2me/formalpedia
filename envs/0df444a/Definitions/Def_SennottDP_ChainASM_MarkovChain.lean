-- Prove2me | Definitions.Def_SennottDP_ChainASM_MarkovChain
-- name    : SennottDP_ChainASM_MarkovChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T14:22:37.131957+00:00
-- url     : https://prove2.me/theorems/5231fa40-3046-46b8-b59e-df45a00e9ed1
-- title:
--   Markov chains with costs on a countable state space: taboo probabilities, first passages, steady state, average cost
-- statement:
--   A **Markov chain with costs** $\Gamma$ on a countable state space $S$ consists of transition probabilities $P_{ij}\ge 0$ with $\sum_j P_{ij}=1$ for every $i\in S$, and a finite nonnegative cost $C(i)$ at every state. From these the following quantities are defined, all with values in $[0,\infty]$.
--
--   1. The $t$-step transition probabilities $P^{(t)}_{ij}$, with $P^{(0)}_{ij}=\delta_{ij}$ and $P^{(t+1)}_{ij}=\sum_k P^{(t)}_{ik}P_{kj}$.
--   2. For a set $G\subseteq S$, the **taboo probability** ${}_GP^{(t)}_{ik}$: the probability of moving from $i$ to $k$ in $t$ slots while none of the intermediate states lies in $G$ (the initial and terminal states may lie in $G$). Thus ${}_GP^{(0)}_{ik}=\delta_{ik}$, ${}_GP^{(1)}_{ik}=P_{ik}$ and ${}_GP^{(t+1)}_{ik}=\sum_{j\notin G}P_{ij}\,{}_GP^{(t)}_{jk}$.
--   3. With $T_{iG}\ge 1$ the first passage time from $i$ to $G$, the probability $P(X_t=k,\,T_{iG}>t\mid X_0=i)$, which is $\delta_{ik}$ at $t=0$ and ${}_GP^{(t)}_{ik}\,\mathbf 1\{k\notin G\}$ for $t\ge 1$.
--   4. The expected number of visits to $k$ during a first passage from $i$ to $G$,
--   $$ {}_Gu_{ik}=\sum_{t\ge 0}P(X_t=k,\,T_{iG}>t\mid X_0=i), $$
--   the expected first passage time $m_{iG}=E[T_{iG}]=\sum_{t\ge0}P(T_{iG}>t)$ (infinite when $P(T_{iG}<\infty)<1$), and the expected first passage cost $c_{iG}=E\big[\sum_{t=0}^{T_{iG}-1}C(X_t)\big]$. We write $m_{ij}=m_{i\{j\}}$, $c_{ij}=c_{i\{j\}}$.
--   5. Communication of states, the communicating class of $z$, irreducibility, positive recurrence ($m_{ii}<\infty$), positive recurrent classes, and the steady state probability $\pi_j=(m_{jj})^{-1}$ (zero when $m_{jj}=\infty$).
--   6. The average cost $J(i)=\limsup_{n\to\infty}\frac1n\sum_{t=0}^{n-1}\sum_jP^{(t)}_{ij}C(j)$ and, for a positive recurrent class $R$, $J_R=\sum_{j\in R}\pi_jC(j)$.
--   7. $\Gamma$ is **$z$ standard** if $m_{iz}<\infty$ and $c_{iz}<\infty$ for all $i$; it is **unichain with $z$ in its positive recurrent class** if it has exactly one positive recurrent class and that class contains $z$.
--
--   These are the objects of Appendix C, Sections C.1–C.3, on which the approximating-sequence results of Sections C.4–C.5 are stated.
--
--   **Formalization Note** Probabilities and expectations are computed from $P$ as sums in $[0,\infty]$; $m_{iG}$ and $c_{iG}$ are defined for every $i$ as the expectations above (the book uses $c_{iG}$ only when $m_{iG}<\infty$). The average cost is a $\limsup$; on a positive recurrent class and on a finite state space the limit exists.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 292–302, Sections C.1–C.3 (taboo probabilities p. 295, (C.1)–(C.4), (C.11), Proposition C.2.1(i), Definition C.2.5, unichain p. 302)

import Mathlib

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.ChainASM

/-! Markov chains with costs (Sennott 1999, Appendix C.1–C.2, pp. 292–301). A Markov chain `Γ`
on a countable state space `S` is a transition matrix `P` whose rows are probability
distributions, together with a finite nonnegative cost `C(i)` at every state. All probabilistic
quantities are computed from `P` alone, in `[0, ∞]`. -/

/-- A Markov chain with costs `Γ` on the state space `S` (pp. 292 and 298): transition
probabilities `P_{ij}` with `∑_j P_{ij} = 1` for every `i`, and a finite nonnegative cost `C(i)`
attached to each state. -/
structure MC (S : Type*) where
  /-- the transition probability `P_{ij}` -/
  P : S → S → ℝ≥0∞
  /-- each row is a probability distribution: `∑_j P_{ij} = 1` -/
  P_sum : ∀ i, ∑' j, P i j = 1
  /-- the (finite, nonnegative) cost `C(i)` -/
  C : S → ℝ≥0

namespace MC

variable {S : Type*} (Γ : MC S)

open Classical in
/-- The `t`-step transition probabilities `P^{(t)}_{ij}`, `P^{(0)}_{ij} = δ_{ij}` (p. 292). -/
noncomputable def nStep : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | t + 1, i, j => ∑' k, nStep t i k * Γ.P k j

open Classical in
/-- The taboo probability `_G P^{(t)}_{ik}` (p. 295): the probability of going from `i` to `k` in
`t` slots with none of the intermediate states `X_1, …, X_{t-1}` in `G` (the initial and the
terminal state may lie in `G`). `_G P^{(0)}_{ik} = δ_{ik}`, `_G P^{(1)}_{ik} = P_{ik}`, and
`_G P^{(t+1)}_{ik} = ∑_{j ∉ G} P_{ij} {}_G P^{(t)}_{jk}` for `t ≥ 1` ((C.2), p. 296). -/
noncomputable def tabooProb (G : Set S) : ℕ → S → S → ℝ≥0∞
  | 0, i, k => if i = k then 1 else 0
  | 1, i, k => Γ.P i k
  | t + 2, i, k => ∑' j, if j ∈ G then 0 else Γ.P i j * tabooProb G (t + 1) j k

open Classical in
/-- `P(X_t = k, T_{iG} > t | X_0 = i)`, where `T_{iG} ≥ 1` is the first passage time from `i`
to the nonempty set `G` (p. 295): `δ_{ik}` for `t = 0`, and for `t ≥ 1` the taboo probability
`_G P^{(t)}_{ik}` restricted to `k ∉ G`. -/
noncomputable def avoidProb (G : Set S) (t : ℕ) (i k : S) : ℝ≥0∞ :=
  if t = 0 then (if i = k then 1 else 0) else if k ∈ G then 0 else Γ.tabooProb G t i k

/-- `_G u_{ik}`, the expected number of visits to `k` during a first passage from `i` to `G`
(p. 295): the visits at the times `0 ≤ t < T_{iG}`, i.e. `∑_{t ≥ 0} P(X_t = k, T_{iG} > t)`.
For `k ∈ G` this is `δ_{ik}` (so `0` if `i ∉ G`), and for `k ∉ G` it is
`δ_{ik} + ∑_{t ≥ 1} {}_G P^{(t)}_{ik}`. -/
noncomputable def visits (G : Set S) (i k : S) : ℝ≥0∞ :=
  ∑' t : ℕ, Γ.avoidProb G t i k

/-- `m_{iG} = E[T_{iG}]`, the expected first passage time from `i` to `G` (p. 295), computed as
`∑_{t ≥ 0} P(T_{iG} > t)`. It equals `∞` whenever `P(T_{iG} < ∞) < 1`, as in the book.
`m_{ij}` is `m_{i\{j\}}`. -/
noncomputable def meanPassage (G : Set S) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' k, Γ.avoidProb G t i k

/-- `c_{iG}`, the expected cost of a first passage from `i` to `G` (p. 298):
`E[∑_{t=0}^{T_{iG}-1} C(X_t) | X_0 = i] = ∑_{t ≥ 0} ∑_k P(X_t = k, T_{iG} > t) C(k)`. The book
speaks of `c_{iG}` only when `m_{iG} < ∞`; there it is this quantity. -/
noncomputable def passageCost (G : Set S) (i : S) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' k, Γ.avoidProb G t i k * (Γ.C k : ℝ≥0∞)

/-- `i` leads to `j`: `P^{(t)}_{ij} > 0` for some `t ≥ 0` (p. 293). -/
def LeadsTo (i j : S) : Prop :=
  ∃ t, 0 < Γ.nStep t i j

/-- `i` and `j` communicate (p. 293). -/
def Communicate (i j : S) : Prop :=
  Γ.LeadsTo i j ∧ Γ.LeadsTo j i

/-- The communicating class of `z`. -/
def commClass (z : S) : Set S :=
  {j | Γ.Communicate z j}

/-- `Γ` is irreducible: all states communicate (p. 293). -/
def Irreducible : Prop :=
  ∀ i j, Γ.Communicate i j

/-- `i` is positive recurrent: the expected return time `m_{ii}` is finite (p. 293; finiteness
of `m_{ii}` forces `P(T < ∞) = 1`). A state is transient or null recurrent exactly when
`m_{ii} = ∞`. -/
def PosRecurrent (i : S) : Prop :=
  Γ.meanPassage {i} i < ⊤

/-- `R` is a positive recurrent class: the communicating class of a positive recurrent state
(p. 293; positive recurrence is a class property). -/
def IsPosRecClass (R : Set S) : Prop :=
  ∃ i, Γ.PosRecurrent i ∧ R = Γ.commClass i

/-- The steady state probability `π_j = (m_{jj})^{-1}`, which is `0` when `m_{jj} = ∞` (p. 294). -/
noncomputable def steadyState (j : S) : ℝ≥0∞ :=
  (Γ.meanPassage {j} j)⁻¹

/-- The average cost from `X_0 = i`, `J(i) = limsup_{n→∞} J^{(n)}_i` with
`J^{(n)}_i = (1/n) E[∑_{t=0}^{n-1} C(X_t) | X_0 = i] = ∑_j C(j) Q^{(n)}_{ij}` ((C.11), p. 298),
a value in `[0, ∞]`. (On a positive recurrent class and on a finite state space the limit
exists, Proposition C.2.1(i) and Section C.3.) -/
noncomputable def avgCost (i : S) : ℝ≥0∞ :=
  limsup (fun n : ℕ =>
    (∑ t ∈ Finset.range n, ∑' j, Γ.nStep t i j * (Γ.C j : ℝ≥0∞)) / (n : ℝ≥0∞)) atTop

/-- The average cost on a positive recurrent class `R`, `J_R = ∑_{j ∈ R} π_j C(j)`
(Proposition C.2.1(i), p. 298), a value in `[0, ∞]`. -/
noncomputable def classAvgCost (R : Set S) : ℝ≥0∞ :=
  ∑' j : R, Γ.steadyState j * (Γ.C j : ℝ≥0∞)

/-- Definition C.2.5, p. 301: `Γ` is `z` standard if `m_{iz} < ∞` and `c_{iz} < ∞` for all
`i ∈ S`. -/
def IsZStandard (z : S) : Prop :=
  ∀ i, Γ.meanPassage {z} i < ⊤ ∧ Γ.passageCost {z} i < ⊤

/-- `Γ` is unichain (exactly one positive recurrent class, p. 302) and `z` is an element of its
positive recurrent class. -/
def IsUnichainWith (z : S) : Prop :=
  ∃ R, Γ.IsPosRecClass R ∧ z ∈ R ∧ ∀ R', Γ.IsPosRecClass R' → R' = R

end MC

end SennottDP.ChainASM



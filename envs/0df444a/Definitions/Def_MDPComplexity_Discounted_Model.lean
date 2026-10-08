-- Prove2me | Definitions.Def_MDPComplexity_Discounted_Model
-- name    : MDPComplexity_Discounted_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:33:13.981987+00:00
-- url     : https://prove2.me/theorems/d9083b1f-9ef8-4550-9e7a-4a339af044c1
-- title:
--   §2–§3 (pp. 444–447): deterministic stationary MDP, policies δ(s, t), discounted cost, sigmas, walks, and the min-plus matrices A and B_j
-- statement:
--   This file fixes the objects of the infinite-horizon discounted deterministic problem of Papadimitriou and Tsitsiklis.
--
--   1. **Deterministic stationary Markov decision process.** A finite set $S$ of states and, at each state $s$, a finite nonempty set $D_s$ of decisions. Decision $i\in D_s$ costs $c(s,i)\in\mathbb R$ and leads with certainty to the state $\mathrm{next}(s,i)$. Equivalently, it is a directed graph $G=(V,A)$ with one node per state and one arc $s\to\mathrm{next}(s,i)$ of weight $c(s,i)$ per decision, so parallel arcs and loops are allowed.
--   2. **Policies.** A policy $\delta$ assigns a decision $\delta(s,t)\in D_s$ to every state $s$ and time $t=0,1,2,\dots$; it is *stationary* if $\delta(s,t)=\delta(s,0)$ for all $s,t$. From the initial state $s_0$ the policy generates the states $s_{t+1}=\mathrm{next}(s_t,\delta(s_t,t))$.
--   3. **Discounted cost and its optimum.** For $\beta\in\mathbb R$,
--   $$J_\beta(\delta)=\sum_{t=0}^{\infty}\beta^t\,c\bigl(s_t,\delta(s_t,t)\bigr),\qquad J^*_\beta(s_0)=\inf_{\delta}J_\beta(\delta),$$
--   the infimum running over **all** policies $\delta(s,t)$, stationary or not.
--   4. **Sigma.** A sigma is a walk $w_0=s_0,w_1,\dots,w_N$ along decisions $e_t\in D_{w_t}$ whose nodes $w_0,\dots,w_{N-1}$ are distinct and whose last node repeats an earlier one, $w_N=w_j$ with $0\le j<N$: the walk from $s_0$ up to the first repetition of a node. It consists of a prefix of $j$ arcs and a cycle of $l=N-j\ge1$ arcs. Its *discounted cost* is the discounted cost $\sum_t\beta^t c_t$ of the infinite walk that follows the sigma and then repeats its cycle forever.
--   5. **Walks.** A $j$-arc walk from $u$ to $v$ is a sequence of nodes $w_0=u,\dots,w_j=v$ and decisions $e_t\in D_{w_t}$ with $\mathrm{next}(w_t,e_t)=w_{t+1}$; nodes may repeat. Its discounted length is $\sum_{t<j}\beta^t c(w_t,e_t)$.
--   6. **Min-plus matrices.** In the min-plus semiring (addition is $\min$, multiplication is $+$, zero is $+\infty$), $A_{uv}$ is the least cost of a decision leading from $u$ to $v$ and $+\infty$ if there is none; $rA$ multiplies every finite entry by $r$; and
--   $$B_0=I,\qquad B_{j+1}=B_j\otimes\beta^jA,\qquad\text{so } B_j=A\otimes\beta A\otimes\cdots\otimes\beta^{j-1}A,$$
--   where $I$ is the min-plus identity ($0$ on the diagonal, $+\infty$ off it).
--
--   These are the objects in which the paper's Theorem 4 (the discounted deterministic problem is in NC) is proved: the optimal discounted cost is the least discounted cost of a sigma, and that least cost is read off the entries of the products $B_j$.
--
--   **Formalization Note** The paper writes $D_s$ as "a finite set"; we require it to be nonempty, since a policy must choose a decision. The paper's sigma $(u_0,\dots,u_k,v_1,\dots,v_l,v_1)$ corresponds to $j=k+1$ and $N=k+1+l$; we also admit $j=0$, the sigma whose cycle passes through $u_0$ ("a path from $u_0$ until the first repetition of a node"), which the printed form omits. Paper indices $i=1,\dots$ become Lean indices from $0$. The sigma's and walk's sequences are indexed by $\mathbb N$; only their first $N+1$ (resp. $j+1$) nodes and $N$ (resp. $j$) decisions are used. The paper defines $B_1,\dots,B_n$ but uses $B_0$; we take $B_0$ to be the min-plus identity. Matrix entries live in `Tropical (WithTop ℝ)`, with `⊤` playing $+\infty$.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 444 (§2, Markov Decision Processes), p. 445 (§3, Deterministic problems), p. 446 (§3, The infinite horizon, discounted case; matrix A in the paragraph before Theorem 3), p. 447 (B_j)

import Mathlib

namespace MDPComplexity.Discounted

open Finset

/-- §2 (p. 444) and §3 "Deterministic problems." (p. 445): a finite, stationary, deterministic
Markov decision process. `S` is the finite set of states; `D s` is the finite, nonempty set of
decisions at `s`; decision `i ∈ D s` costs `c s i` and leads with certainty to `next s i`
(the only transition probabilities are 0 and 1). In the graph `G = (V, A)` of p. 445 the decision
`i` at `s` is the arc `s → next s i` of weight `c s i`, so parallel arcs and loops are allowed. -/
structure DetMDP (S : Type) [Fintype S] [DecidableEq S] where
  D : S → Type
  [instFintype : ∀ s, Fintype (D s)]
  [instNonempty : ∀ s, Nonempty (D s)]
  next : (s : S) → D s → S
  c : (s : S) → D s → ℝ

attribute [instance] DetMDP.instFintype DetMDP.instNonempty

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A policy `δ(s, t)` (p. 444): a decision for every state `s` and every time `t = 0, 1, 2, …`. -/
def DetMDP.Policy (M : DetMDP S) : Type := (s : S) → ℕ → M.D s

/-- A policy is stationary if `δ(s, t)` is independent of `t` (p. 444). -/
def DetMDP.IsStationary (M : DetMDP S) (δ : M.Policy) : Prop :=
  ∀ (s : S) (t : ℕ), δ s t = δ s 0

/-- The state `s_t` at time `t` when the process starts at `s₀` and follows `δ`. -/
def DetMDP.path (M : DetMDP S) (s₀ : S) (δ : M.Policy) : ℕ → S
  | 0 => s₀
  | t + 1 => M.next (M.path s₀ δ t) (δ (M.path s₀ δ t) t)

/-- The cost `c(s_t, δ(s_t, t))` incurred at time `t`. -/
def DetMDP.stageCost (M : DetMDP S) (s₀ : S) (δ : M.Policy) (t : ℕ) : ℝ :=
  M.c (M.path s₀ δ t) (δ (M.path s₀ δ t) t)

/-- The discounted cost `Σ_{t=0}^{∞} c(s_t, δ(s_t, t)) β^t` (p. 444) of the policy `δ` from `s₀`. -/
noncomputable def DetMDP.discCost (M : DetMDP S) (β : ℝ) (s₀ : S) (δ : M.Policy) : ℝ :=
  ∑' t : ℕ, β ^ t * M.stageCost s₀ δ t

/-- The optimal discounted cost from `s₀`: the infimum over **all** policies `δ(s, t)`. -/
noncomputable def DetMDP.optDisc (M : DetMDP S) (β : ℝ) (s₀ : S) : ℝ :=
  ⨅ δ : M.Policy, M.discCost β s₀ δ

/-- A sigma (p. 446): a walk `w 0 = s₀, w 1, …, w N` along decisions `e t ∈ D (w t)`
(`next (w t) (e t) = w (t + 1)` for `t < N`) whose nodes `w 0, …, w (N - 1)` are distinct and whose
last node repeats an earlier one, `w N = w j` with `j < N`: the walk from `u₀` up to the first
repetition of a node. In the paper's notation `(u_0, …, u_k, v_1, …, v_l, v_1)` one has `j = k + 1`
and `N = k + 1 + l`; `j = 0` is the sigma whose cycle passes through `u₀`. Only the values of
`w` at `0, …, N` and of `e` at `0, …, N - 1` matter. -/
structure DetMDP.Sigma (M : DetMDP S) (s₀ : S) where
  N : ℕ
  j : ℕ
  w : ℕ → S
  e : (t : ℕ) → M.D (w t)
  start : w 0 = s₀
  step : ∀ t < N, M.next (w t) (e t) = w (t + 1)
  distinct : ∀ a < N, ∀ b < N, w a = w b → a = b
  j_lt : j < N
  closes : w N = w j

/-- The cost `c(w_t, e_t)` of the `t`-th arc of a sigma (`t < N`). -/
def DetMDP.Sigma.arcCost {M : DetMDP S} {s₀ : S} (P : M.Sigma s₀) (t : ℕ) : ℝ :=
  M.c (P.w t) (P.e t)

/-- The index, among the arcs `0, …, N - 1` of the sigma, of the arc taken at time `t` by the
infinite walk that follows the sigma and then repeats its cycle `j, …, N - 1` forever. -/
def DetMDP.Sigma.arcIdx {M : DetMDP S} {s₀ : S} (P : M.Sigma s₀) (t : ℕ) : ℕ :=
  if t < P.j then t else P.j + (t - P.j) % (P.N - P.j)

/-- The discounted cost of a sigma (p. 446): the discounted cost `Σ_t β^t c_t` of the infinite walk
that follows the sigma and repeats its cycle forever. -/
noncomputable def DetMDP.Sigma.cost {M : DetMDP S} {s₀ : S} (P : M.Sigma s₀) (β : ℝ) : ℝ :=
  ∑' t : ℕ, β ^ t * P.arcCost (P.arcIdx t)

/-- A walk with `j` arcs from `u` to `v`: nodes `w 0 = u, …, w j = v` and decisions
`e t ∈ D (w t)` with `next (w t) (e t) = w (t + 1)` for `t < j`. Nodes may repeat. -/
structure DetMDP.Walk (M : DetMDP S) (j : ℕ) (u v : S) where
  w : ℕ → S
  e : (t : ℕ) → M.D (w t)
  start : w 0 = u
  finish : w j = v
  step : ∀ t < j, M.next (w t) (e t) = w (t + 1)

/-- The discounted length `Σ_{t<j} β^t c(w_t, e_t)` of a `j`-arc walk. -/
def DetMDP.Walk.cost {M : DetMDP S} {j : ℕ} {u v : S} (W : M.Walk j u v) (β : ℝ) : ℝ :=
  ∑ t ∈ range j, β ^ t * M.c (W.w t) (W.e t)

/-- The matrix `A` (p. 446): its `(u, v)` entry is the least cost of a decision leading from `u`
to `v`, and `∞` if there is none. Entries live in the min-plus semiring `Tropical (WithTop ℝ)`,
where addition is `min`, multiplication is `+`, and `0 = trop ⊤` is `∞`. -/
noncomputable def DetMDP.A (M : DetMDP S) : Matrix S S (Tropical (WithTop ℝ)) :=
  fun u v => ∑ i : M.D u, if M.next u i = v then Tropical.trop ((M.c u i : ℝ) : WithTop ℝ) else 0

/-- `r A`: every finite entry of `A` multiplied by `r`; `∞` entries stay `∞`. -/
noncomputable def DetMDP.scaledA (M : DetMDP S) (r : ℝ) : Matrix S S (Tropical (WithTop ℝ)) :=
  fun u v => Tropical.trop (WithTop.map (fun x : ℝ => r * x) (Tropical.untrop (M.A u v)))

/-- `B_j` (p. 447): the min-plus product `A ⊗ βA ⊗ ⋯ ⊗ β^{j−1}A`; `B_0` is the min-plus identity
(`0` on the diagonal, `∞` elsewhere). -/
noncomputable def DetMDP.B (M : DetMDP S) (β : ℝ) : ℕ → Matrix S S (Tropical (WithTop ℝ))
  | 0 => 1
  | j + 1 => M.B β j * M.scaledA (β ^ j)

end MDPComplexity.Discounted



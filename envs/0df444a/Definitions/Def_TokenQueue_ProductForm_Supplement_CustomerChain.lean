-- Prove2me | Definitions.Def_TokenQueue_ProductForm_Supplement_CustomerChain
-- name    : TokenQueue_ProductForm_Supplement_CustomerChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:18:07.684717+00:00
-- url     : https://prove2.me/theorems/7fc07930-544c-46ad-8470-bd58759d2a0b
-- title:
--   §3 and §5, pp. 3–5, 9–11 — customer-level chain, descriptor, counts N_j^(c), N^(c), M^(c), θ, G, and the LSTs of W_c and S_c
-- statement:
--   This item builds the **customer-level** model of the token-based central queue of §3 (pp. 3–5), on top of the published descriptor-level model, together with the performance measures of §5.
--
--   1. **States.** A customer-level state $y$ is the list of the customers present, oldest first; each customer is its type $c$ and either the token $t$ it holds (active) or nothing (inactive). A state is *valid* when the held tokens are distinct, each held token lies in its holder's $\mathcal T_c$, and every compatible token of an inactive customer is held by a customer ahead of it (p. 3–4).
--   2. **Rates.** From $y$, with $S$ the set of held (unavailable) tokens: a type-$c$ customer arrives at rate $\lambda_c$; if $\mathcal T_c\subseteq S$ it joins the end of the queue inactive, otherwise it claims $t\in\mathcal T_c\setminus S$ with the assignment-rule probability. The active customer holding $T_j$, the $j$-th token in arrival order of the holders, departs at rate $\eta(\phi(y))\,s_j(T_1,\dots,T_j)$, $\phi(y)$ the number of customers; its token goes to the longest-waiting inactive customer whose type is compatible with it (that customer keeps its place), or becomes available. $q(y,y')$ sums the rates of the transitions from $y$ to $y'$.
--   3. **Stationary law.** $Q$ is a stationary law when $Q\ge0$, $\sum_yQ(y)=1$, $Q$ vanishes off valid states, rows and inflows are summable, and $Q(y)\sum_{y'}q(y,y')=\sum_{y'}Q(y')q(y',y)$ for all $y$.
--   4. **Descriptor and counts.** The descriptor $\mathrm{desc}(y)=(T_1,n_1,\dots,T_i,n_i)$ lists the held tokens in arrival order of their holders and the numbers of inactive customers between consecutive holders (after the last one for $n_i$). $g_j$ is the type of the holder of $T_j$; $N^{(c)}_j$ the number of inactive type-$c$ customers between the holders of $T_j$ and $T_{j+1}$; $N^{(c)}$ the number of inactive type-$c$ customers; $M^{(c)}$ the number of type-$c$ customers (p. 5).
--   5. **Section 5 quantities.** $\theta_{c,j}=\lambda_c\mathbb 1\{c\in\mathcal U(\{T_1,\dots,T_j\})\}/\lambda_{\mathcal U(\{T_1,\dots,T_j\})}$; $G_{c_1,\dots,c_i}(x)=Q(g_1=c_1,\dots,g_i=c_i\mid\mathrm{desc}=x)$; $\pi((0))=(\sum_x w(x))^{-1}$ with $w$ the published weights (10); and the common factor
--   $$\pi((0))\frac{\Pi_\lambda(\{T_1,\dots,T_i\})}{\Pi_k(T_1,\dots,T_i)}\prod_{j=1}^{i}\frac1{\eta(j)}\prod_{j=1}^{n_1+\dots+n_i}\frac1{\eta(i+j)}.$$
--   6. **Time-till-token and sojourn time.** A type-$c$ customer is tagged on arrival to a state drawn from $Q$ (Poisson arrivals see the stationary law); the tagged chain follows the customer-level dynamics and tracks the tagged customer's position. For $\operatorname{Re}s>0$, $\mathbb E[e^{-sW_c}]$ and $\mathbb E[e^{-sS_c}]$ are the Laplace–Stieltjes transforms of the first time the tagged customer holds a token, respectively has departed, computed as the sum over all first-passage jump paths $z_0\to\dots\to z_m$ of $\prod_k q(z_k,z_{k+1})/(s+q(z_k))$, $q(z)$ the total exit rate.
--   7. **FIFO within a type** (hypothesis of Theorem 7): in every state reachable from the empty system, a type-$c$ customer has departure rate $0$ while an earlier type-$c$ customer is present.
--
--   These objects let the §5 results be stated for the queue's actual dynamics rather than for a formula: the PGFs and LSTs are expectations under a stationary law of the customer-level chain.
--
--   **Formalization Note** Customer-level states are lists `List (C × Option T)`; the descriptor and the counts are computed from them; validity is a predicate (the stationary law vanishes off it) rather than a subtype. Rates are forward (§3), never defined from a balance equation. $\theta$ uses Lean's $x/0=0$ when $\lambda_{\mathcal U}=0$ (then $\theta=0$ for every type), and $G$ is $0$ when $Q(\mathrm{desc}=x)=0$. The first-passage transform includes the empty path (weight $1$ when the start state is already in the target), so a customer that claims a token on arrival has $W_c=0$.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, pp. 3–5, §3 (model, state descriptor, Further notation); pp. 9–11, §5 (θ_c,j, G, W_c, S_c, Theorem 7's FIFO hypothesis); p. 7, (11)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_TokenQueue_ProductForm_Model

namespace TokenQueue.ProductForm.Supplement

noncomputable section

open Finset

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

/-! ### The customer-level state (§3, pp. 3–4) -/

/-- A customer-level state: the customers present, in order of arrival (oldest first); each
customer is its type and `some t` if it holds token `t` (active), `none` if it holds no token
(inactive). The empty list is the empty system. -/
abbrev CState (C T : Type) := List (C × Option T)

/-- The tokens held in `y`, in arrival order of their holders (`T₁,…,T_i`). -/
def heldToks (y : CState C T) : List T := y.filterMap Prod.snd

/-- The set of unavailable tokens `𝒯 \ 𝒯^{(a)}` in state `y`: the tokens held. -/
def held (y : CState C T) : Finset T := (heldToks y).toFinset

/-- The invariant of the customer-level states (p. 3–4): held tokens are pairwise distinct; a held
token is compatible with its holder; an inactive customer's compatible tokens are all held by
customers ahead of it (an arriving customer only waits when no compatible token is available, and
a released token goes to the longest-waiting compatible inactive customer). -/
def Valid (P : Params C T) (y : CState C T) : Prop :=
  (heldToks y).Nodup ∧
  (∀ i (h : i < y.length), ∀ t, (y[i]'h).2 = some t → t ∈ P.tok (y[i]'h).1) ∧
  (∀ i (h : i < y.length), (y[i]'h).2 = none → P.tok (y[i]'h).1 ⊆ held (y.take i))

/-- Hand a released token `t` to the first (= longest-waiting) inactive customer whose type is
compatible with `t`; if there is none, the list is unchanged and `t` becomes available. -/
def passToken (P : Params C T) (t : T) : CState C T → CState C T
  | [] => []
  | (c, none) :: l => if t ∈ P.tok c then (c, some t) :: l else (c, none) :: passToken P t l
  | (c, some u) :: l => (c, some u) :: passToken P t l

/-- The departure rate of the customer at (0-based) position `i` of `y` (Condition 2, (3)):
`η(φ(y)) s_j(T₁,…,T_j)` if it holds a token, `T₁,…,T_j` being the tokens held by it and the
active customers ahead of it, and `0` if it holds none. `φ(y)` is the number of customers. -/
def depRate (P : Params C T) (y : CState C T) (i : ℕ) : ℝ :=
  match y[i]? with
  | some (_, some _) => P.eta y.length * P.s (heldToks (y.take (i + 1)))
  | _ => 0

/-- The transitions out of `y` (§3, pp. 3–5), as (target, label, rate) triples; the label is
`none` for an arrival and `some i` for the departure of the customer at position `i`.
* A type-`c` arrival (rate `λ_c`) joins the end of the queue without a token if every
  compatible token is unavailable, and otherwise claims the available compatible token `t` with
  the assignment-rule probability, i.e. at rate `λ_c · assign c S t`, `S` the unavailable tokens.
* An active customer at position `i` departs at rate `depRate P y i`; its token passes to the
  longest-waiting compatible inactive customer, or becomes available. -/
def ctrans (P : Params C T) (y : CState C T) : List (CState C T × Option ℕ × ℝ) :=
  let S := held y
  ((univ : Finset C).toList.flatMap fun c =>
    if P.tok c ⊆ S then [(y ++ [(c, none)], none, P.lam c)]
    else (P.tok c \ S).toList.map fun t => (y ++ [(c, some t)], none, P.lam c * P.assign c S t)) ++
  ((List.finRange y.length).flatMap fun i =>
    match (y.get i).2 with
    | none => []
    | some t => [(passToken P t (y.eraseIdx i), some i.val, depRate P y i.val)])

/-- The transition rate `q(y, y')` of the customer-level chain: the total rate of the
transitions out of `y` that land in `y'`. -/
def crate (P : Params C T) (y y' : CState C T) : ℝ :=
  (((ctrans P y).filter (fun e => e.1 = y')).map fun e => e.2.2).sum

/-- `y'` is reachable from `y` through transitions of positive rate. -/
def Reachable (P : Params C T) (y y' : CState C T) : Prop :=
  Relation.ReflTransGen (fun a b => 0 < crate P a b) y y'

/-- `Q` is a stationary law of the customer-level chain on its valid states: a probability
distribution on the states satisfying the invariant, whose rows and inflows are summable, in
global balance with `crate` (the shape of the conclusion of Theorem 1). -/
def IsStationaryLaw (P : Params C T) (Q : CState C T → ℝ) : Prop :=
  (∀ y, 0 ≤ Q y) ∧ HasSum Q 1 ∧ (∀ y, ¬ Valid P y → Q y = 0) ∧
  (∀ y, Summable (fun y' => crate P y y')) ∧
  (∀ y, Summable (fun y' => Q y' * crate P y' y)) ∧
  KellyStochasticNetworks.FullBalance Q (crate P)

/-- `Q(E) = ∑_{y ∈ E} Q(y)`, the probability of an event under `Q`. -/
def prob (Q : CState C T → ℝ) (E : CState C T → Prop) : ℝ :=
  ∑' y, Set.indicator {y | E y} Q y

/-! ### The descriptor and the counts (p. 4, p. 5, p. 10) -/

/-- The blocks of `y`: for each active customer, in arrival order, its type `g_j`, its token
`T_j`, and the types of the inactive customers between it and the next active customer (the
last block runs to the end of the queue). Inactive customers ahead of every active customer
(impossible in a valid state) are dropped. -/
def blocks (y : CState C T) : List (C × T × List C) :=
  y.foldl (fun acc p =>
    match p.2 with
    | none => acc.modifyLast (fun b => (b.1, b.2.1, b.2.2 ++ [p.1]))
    | some t => acc ++ [(p.1, t, [])]) []

/-- The state descriptor `(T₁,n₁,…,T_i,n_i)` of `y` (p. 4). -/
def desc (y : CState C T) : List (T × ℕ) :=
  (blocks y).map fun b => (b.2.1, b.2.2.length)

/-- The types `g₁,…,g_i` of the customers holding `T₁,…,T_i` (Theorem 4, p. 10). -/
def holderTypes (y : CState C T) : List C := (blocks y).map Prod.fst

/-- `N_j^{(c)}`: the number of inactive type-`c` customers between the holders of `T_{j+1}` and
`T_{j+2}` (0-based block index `j`; `0` if there is no such block) (p. 5). -/
def Nseg (y : CState C T) (j : ℕ) (c : C) : ℕ :=
  ((blocks y)[j]?.map fun b => b.2.2.count c).getD 0

/-- `N^{(c)}`: the number of inactive type-`c` customers (p. 5). -/
def Ntot (y : CState C T) (c : C) : ℕ :=
  (y.filter fun p => p.1 = c ∧ p.2 = none).length

/-- `M^{(c)}`: the number of type-`c` customers present (p. 5). -/
def Mtot (y : CState C T) (c : C) : ℕ :=
  (y.filter fun p => p.1 = c).length

/-! ### The quantities of §5 -/

/-- `θ_{c,j} = λ_c 1{c ∈ 𝒰(T₁,…,T_j)} / λ_{𝒰(T₁,…,T_j)}` for the prefix `l = [T₁,…,T_j]`
(Theorem 2, p. 9). -/
def theta (P : Params C T) (l : List T) (c : C) : ℝ :=
  if P.tok c ⊆ l.toFinset then P.lam c / lamU P l.toFinset else 0

/-- `G_{c₁,…,c_i}(x) = Q(g₁ = c₁,…,g_i = c_i | desc = x)`, the conditional law under `Q` of the
types of the token holders given the descriptor (Theorem 4, p. 10); `0` when `Q(desc = x) = 0`. -/
def Gcond (Q : CState C T → ℝ) (x : List (T × ℕ)) (cs : List C) : ℝ :=
  prob Q (fun y => desc y = x ∧ holderTypes y = cs) / prob Q (fun y => desc y = x)

/-- `π((0))` as given by (11): the inverse of the sum of the weights (10) over all states. -/
def piZero (P : Params C T) : ℝ := (∑' x : State T, weight P x)⁻¹

/-- The common factor of (17), (19), (22), (24) at `x = (T₁,n₁,…,T_i,n_i)`:
`π((0)) Π_λ({T₁,…,T_i})/Π_k(T₁,…,T_i) ∏_{j=1}^{i} 1/η(j) ∏_{j=1}^{n₁+⋯+n_i} 1/η(i+j)`. -/
def commonFactor (P : Params C T) (x : List (T × ℕ)) : ℝ :=
  piZero P * (piLam P (toks x) / piK P (toks x)) *
    (∏ j ∈ Icc 1 x.length, (P.eta j)⁻¹) *
    ∏ j ∈ Icc 1 (x.map Prod.snd).sum, (P.eta (x.length + j))⁻¹

/-! ### First-passage Laplace–Stieltjes transforms (§5.3–5.4) -/

/-- The weight of a finite jump path `z = z₀ → z₁ → ⋯ → z_m` (the list `[z₁,…,z_m]`) that
reaches the target `A` for the first time at its last state:
`∏_{k<m} q(z_k, z_{k+1}) / (s + q(z_k))`, `q(z) = ∑_{z'} q(z,z')` the total exit rate; the empty
path has weight `1` if `z ∈ A` and `0` otherwise. -/
def pathWeight {S : Type} (q : S → S → ℝ) (A : S → Bool) (s : ℂ) : S → List S → ℂ
  | z, [] => if A z then 1 else 0
  | z, z' :: l => if A z then 0 else
      ((q z z' : ℝ) : ℂ) / (s + ((∑' w, q z w : ℝ) : ℂ)) * pathWeight q A s z' l

/-- `E_z[e^{−s τ_A}]` for the continuous-time Markov chain with rates `q` started at `z`, `τ_A`
its first hitting time of `A`: the sum of the weights of all first-passage jump paths. -/
def hitLST {S : Type} (q : S → S → ℝ) (A : S → Bool) (s : ℂ) (z : S) : ℂ :=
  ∑' l : List S, pathWeight q A s z l

/-- A state of the chain with one tagged customer: the customer-level state and the position
of the tagged customer (`none` once it has departed). -/
abbrev TState (C T : Type) := CState C T × Option ℕ

/-- The transitions of the tagged chain: those of the customer-level chain, with the tagged
position updated (unchanged by arrivals and by departures behind it, decreased by one by a
departure ahead of it, `none` when the tagged customer departs). -/
def ttrans (P : Params C T) : TState C T → List (TState C T × ℝ)
  | (_, none) => []
  | (y, some p) => (ctrans P y).map fun e =>
      ((e.1, match e.2.1 with
        | none => some p
        | some i => if i = p then none else if i < p then some (p - 1) else some p), e.2.2)

/-- The transition rates of the tagged chain. -/
def trate (P : Params C T) (a b : TState C T) : ℝ :=
  (((ttrans P a).filter (fun e => e.1 = b)).map Prod.snd).sum

/-- The tagged customer holds (or has held) a token. -/
def tokenTaken (a : TState C T) : Bool :=
  match a.2 with
  | none => true
  | some p => ((a.1[p]?).bind Prod.snd).isSome

/-- The tagged customer has departed. -/
def departed (a : TState C T) : Bool := a.2.isNone

/-- The possible states just after a tagged type-`c` customer arrives to `y`, with their
probabilities: it waits at the end of the queue if no compatible token is available, and
otherwise claims the available compatible token `t` with probability `assign c S t`. -/
def arrivalStarts (P : Params C T) (c : C) (y : CState C T) : List (TState C T × ℝ) :=
  let S := held y
  if P.tok c ⊆ S then [((y ++ [(c, none)], some y.length), 1)]
  else (P.tok c \ S).toList.map fun t => ((y ++ [(c, some t)], some y.length), P.assign c S t)

/-- `E[e^{−s W_c}]`: the LST of the time-till-token `W_c` of a type-`c` customer arriving to the
stationary system `Q` (Poisson arrivals see `Q`), `W_c` being the time from its arrival until it
holds a token (§3 p. 5, §5.3). -/
def lstW (P : Params C T) (Q : CState C T → ℝ) (c : C) (s : ℂ) : ℂ :=
  ∑' y, (Q y : ℂ) *
    ((arrivalStarts P c y).map fun e => (e.2 : ℂ) * hitLST (trate P) tokenTaken s e.1).sum

/-- `E[e^{−s S_c}]`: the LST of the sojourn time `S_c` of a type-`c` customer arriving to the
stationary system `Q`, the time from its arrival until it departs (§3 p. 5, §5.4). -/
def lstS (P : Params C T) (Q : CState C T → ℝ) (c : C) (s : ℂ) : ℂ :=
  ∑' y, (Q y : ℂ) *
    ((arrivalStarts P c y).map fun e => (e.2 : ℂ) * hitLST (trate P) departed s e.1).sum

/-- The hypothesis of Theorem 7: in every customer-level state reachable from the empty system,
a type-`c` customer cannot depart while a type-`c` customer that arrived before it is present
(type-`c` customers depart in the order of arrival). -/
def FifoType (P : Params C T) (c : C) : Prop :=
  ∀ y, Reachable P [] y → ∀ i j (hi : i < j) (hj : j < y.length),
    (y[i]'(lt_trans hi hj)).1 = c → (y[j]'hj).1 = c → depRate P y j = 0

end

end TokenQueue.ProductForm.Supplement



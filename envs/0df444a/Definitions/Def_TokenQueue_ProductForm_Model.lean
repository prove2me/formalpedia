-- Prove2me | Definitions.Def_TokenQueue_ProductForm_Model
-- name    : TokenQueue_ProductForm_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:04.954068+00:00
-- url     : https://prove2.me/theorems/f41913b6-38fe-4f91-bb4e-6a917cdc2623
-- title:
--   §3–§4.1, pp. 3–7 — token-based central queue: types, tokens, assignment rule, order-independent rates, state descriptor, forward transition rates, weights (10)
-- statement:
--   The **token-based central queue** has a finite set $\mathcal C$ of customer types and a finite set $\mathcal T=\{t_1,\dots,t_K\}$ of tokens. Type-$c$ customers arrive in a Poisson process of rate $\lambda_c>0$; the total arrival rate is $\lambda=\sum_{c\in\mathcal C}\lambda_c$. A type-$c$ customer can hold only tokens from its compatibility set $\mathcal T_c\subseteq\mathcal T$, and receives service only while it holds a token.
--
--   1. **Assignment rule.** An arrival of type $c$ that finds the set $S$ of tokens unavailable claims an available compatible token $t\in\mathcal T_c\setminus S$ with probability $p_c(S,t)$ (a probability distribution on $\mathcal T_c\setminus S$ when that set is non-empty); if $\mathcal T_c\subseteq S$ it joins the end of the central queue as an *inactive* customer. With $\mathcal U(S)=\{c:\mathcal T_c\subseteq S\}$,
--   $$\lambda_{\mathcal U(S)}=\sum_{c\in\mathcal U(S)}\lambda_c,\qquad \lambda_t(S)=\sum_{c\in\mathcal C}\lambda_c\,p_c(S,t).$$
--   2. **State descriptor.** A state $x=(T_1,n_1,\dots,T_i,n_i)$ lists, in order of arrival, the $i$ active customers by the distinct tokens $T_1,\dots,T_i$ they hold, and the number $n_j$ of inactive customers that arrived between the holders of $T_j$ and $T_{j+1}$ ($n_i$: after $T_i$). The empty state is $(0)$, and $\phi(x)=i+\sum_j n_j$ is the number of customers.
--   3. **Order-independent rates.** Functions $s_j(T_1,\dots,T_j)\ge 0$ and $\eta(n)$ with $\eta(n)>0$ for $n\ge1$ are given; the holder of $T_j$ in state $x$ leaves at rate $\mu_{T_j}(x)=\eta(\phi(x))\,s_j(T_1,\dots,T_j)$, (3), and $\mu(x)=\sum_j\mu_{T_j}(x)$. Write $k(T_1,\dots,T_i)=\sum_{j=1}^i s_j(T_1,\dots,T_j)$, $k(\emptyset)=0$.
--   4. **Conditions.** *Condition 1* (assignment condition, (2)): $\Pi_\lambda(T_1,\dots,T_i)=\prod_{j=1}^i\lambda_{T_j}(\{T_1,\dots,T_{j-1}\})$ is invariant under permutations of distinct tokens. *Condition 2* (order-independent condition): $k(T_1,\dots,T_i)$ is invariant under permutations.
--   5. **Transitions (§4.1).** From $y=(T_1,n_1,\dots,T_i,n_i)$: an inactive arrival leads to $(\dots,T_i,n_i+1)$ at rate $\lambda_{\mathcal U(\{T_1,\dots,T_i\})}$ (for $y\ne(0)$); an arrival claiming $t\notin\{T_1,\dots,T_i\}$ leads to $(\dots,T_i,n_i,t,0)$ at rate $\lambda_t(\{T_1,\dots,T_i\})$. When the holder of $T_j$ leaves (rate $\mu_{T_j}(y)$), the token passes to the first waiting customer behind it that is compatible with it: a customer waiting after $T_l$ ($l\ge j$) is incompatible with $T_j$ with probability $\lambda_{\mathcal U(\{T_1,\dots,T_l\}\setminus\{T_j\})}/\lambda_{\mathcal U(\{T_1,\dots,T_l\})}$, independently. The customers passed over stay in front of $T_j$; those of $T_j$'s own portion join the previous portion. If nobody is compatible, $T_j$ is released. The rate $q(y,x)$ is the total rate of these transitions from $y$ into $x$.
--   6. **Weights (10).** With $\alpha_j=\lambda_{\mathcal U(\{T_1,\dots,T_j\})}/k(T_1,\dots,T_j)$ and $\Pi_k(T_1,\dots,T_i)=\prod_{j=1}^i k(T_1,\dots,T_j)$,
--   $$w(x)=\frac{\Pi_\lambda(\{T_1,\dots,T_i\})}{\Pi_k(T_1,\dots,T_i)}\prod_{j=1}^i\alpha_j^{n_j}\prod_{j=1}^{\phi(x)}\frac1{\eta(j)},\qquad w((0))=1.$$
--   7. **The paper's backward objects (§4.1.2–4.1.4).** $\beta_k(T)=\lambda_{\mathcal U(\{T_1,\dots,T_k\})}/\lambda_{\mathcal U(\{T_1,\dots,T_k,T\})}$, $\beta_0(T)=0$, (6); $\mathrm{release}_{k,n}(x,T)=(T_1,n_1,\dots,T_k,n_k-n,T,n,T_{k+1},\dots,T_i,n_i)$ and $r_{k,n}(x,T)=\beta_k(T)^n\beta_{k+1}(T)^{n_{k+1}}\cdots\beta_i(T)^{n_i}$; $\mathrm{shift}_{k,n}(x,T_j)$ and $s_{k,n}(x,T_j)=\beta_k(T_j)^n\beta_{k+1}(T_j)^{n_{k+1}}\cdots\beta_{j-1}(T_j)^{n_{j-1}}(1-\beta_{j-1}(T_j))$ for $0\le k\le j-1$; and the right-hand side of the global balance equations (8)–(9).
--
--   These are the objects of Theorem 1 and of the partial balance equations (12)–(14) used to prove it.
--
--   **Formalization Note** Rates are real numbers. A state is a list of (token, count) pairs with distinct tokens (`State T`); infeasible descriptors are kept, since the weights vanish on them. `Params.s` takes the list $[T_1,\dots,T_j]$, which builds in item 1 of Condition 2; the departure rates are *defined* by (3), so Condition 2 is items 2 (`Condition2`) and 3 plus $s\ge0$ (in `Params.Standing`). `Params.Standing` also requires $\mathcal T_c\ne\emptyset$ for every type, an **added** assumption: a type with no compatible token could not be placed in the descriptor, and (1) at $S=\emptyset$ needs $\lambda_{\mathcal U(\emptyset)}=0$. `KPos` ($k>0$ on non-empty sequences of distinct tokens) is an **added** assumption: the weights divide by $k$. `transitions` lists the forward transitions with their rates; transitions of probability $0$ may appear with rate $0$. Lean's $x/0=0$ makes $\beta$ and the reclaim probabilities $0$ when $\lambda_{\mathcal U}=0$, which only happens on portions that must be empty in a feasible state. **Correction:** p. 6 defines $\mathrm{shift}_{k,n}(x,T_j)$ for $1\le k$, $k+1<j$, but (8) and (14) sum over $0\le k\le j-1$; for $k=0$ we use $n_0=0$, $\beta_0=0$ (p. 24), and for $k=j-1$ the state is $(T_1,n_1,\dots,T_{j-1},n_{j-1}-n,T_j,n+1+n_j,T_{j+1},\dots,T_i,n_i)$. Indices $j$ in `shift`/`sfac` are the paper's 1-based ones; positions in `muTok` and `departures` are 0-based.
-- source:
--   Ayesta, Bodas, Dorsman, Verloop, A token-based central queue with order-independent service rates, arXiv:1902.02137v1, pp. 3–7, §3 (model), Condition 1 (2), Condition 2 (3), (4), §4.1 (transitions, (5)–(7)), §4.1.4 ((8)–(9)), Theorem 1 ((10)); p. 24 (n₀ = 0, k(∅) = 0)

import Mathlib

namespace TokenQueue.ProductForm

noncomputable section

open Finset BigOperators

/-! ### The data of the model (§3, pp. 3–5) -/

/-- The parameters of a token-based central queue with customer types `C` and tokens `T`
(Ayesta–Bodas–Dorsman–Verloop, §3, pp. 3–5).

* `lam c` is the Poisson arrival rate `λ_c` of type-`c` customers;
* `tok c` is the set `𝒯_c` of tokens compatible with type `c`;
* `assign c S t` is the randomised assignment rule: the probability that an arriving type-`c`
  customer claims token `t` when `S` is the set of unavailable tokens;
* `s l` is the function `s_j(T₁,…,T_j)` of Condition 2, evaluated at the list
  `l = [T₁,…,T_j]` (so `s_j(T₁,…,T_i) = s_j(T₁,…,T_j)` holds by construction);
* `eta n` is the function `η(n)` of Condition 2. -/
structure Params (C T : Type) where
  lam : C → ℝ
  tok : C → Finset T
  assign : C → Finset T → T → ℝ
  s : List T → ℝ
  eta : ℕ → ℝ

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

/-- The standing assumptions of §3: positive arrival rates (p. 3); every type has at least one
compatible token (an *added* assumption, see the natural-language statement); the assignment
rule is a probability distribution on the available compatible tokens `𝒯_c \ S` whenever that
set is non-empty (p. 3); `s ≥ 0` (Condition 2, item 1) and `η(j) > 0` for `j ≥ 1`
(Condition 2, item 3). -/
def Params.Standing (P : Params C T) : Prop :=
  (∀ c, 0 < P.lam c) ∧
  (∀ c, (P.tok c).Nonempty) ∧
  (∀ c S t, 0 ≤ P.assign c S t) ∧
  (∀ c S t, t ∉ P.tok c \ S → P.assign c S t = 0) ∧
  (∀ c S, (P.tok c \ S).Nonempty → ∑ t ∈ P.tok c \ S, P.assign c S t = 1) ∧
  (∀ l, 0 ≤ P.s l) ∧
  (∀ j, 1 ≤ j → 0 < P.eta j)

/-- The total arrival rate `λ = ∑_{c ∈ 𝒞} λ_c` (p. 3). -/
def lamTot (P : Params C T) : ℝ := ∑ c, P.lam c

/-- `λ_{𝒰(S)} = ∑_{c ∈ 𝒰(S)} λ_c`, where `𝒰(S) = {c : 𝒯_c ⊆ S}` is the set of types that can
claim tokens only from `S` (p. 4). -/
def lamU (P : Params C T) (S : Finset T) : ℝ :=
  ∑ c ∈ univ.filter (fun c => P.tok c ⊆ S), P.lam c

/-- `λ_t(S) = ∑_c λ_c · P(type `c` claims `t` | unavailable set `S`)`, the rate at which arriving
customers claim token `t` when `S` is the set of unavailable tokens (p. 4). -/
def lamTok (P : Params C T) (S : Finset T) (t : T) : ℝ :=
  ∑ c, P.lam c * P.assign c S t

/-- `k(T₁,…,T_i) = ∑_{j=1}^{i} s_j(T₁,…,T_j)` (Condition 2, item 2); `k([]) = 0`. -/
def kfun (P : Params C T) (l : List T) : ℝ :=
  ∑ j ∈ range l.length, P.s (l.take (j + 1))

/-- `Π_λ({T₁,…,T_i}) = ∏_{j=1}^{i} λ_{T_j}({T₁,…,T_{j-1}})` (Theorem 1, p. 7). -/
def piLam (P : Params C T) (l : List T) : ℝ :=
  ∏ j : Fin l.length, lamTok P (l.take j).toFinset (l.get j)

/-- `Π_k(T₁,…,T_i) = ∏_{j=1}^{i} k(T₁,…,T_j)` (Theorem 1, p. 7). -/
def piK (P : Params C T) (l : List T) : ℝ :=
  ∏ j : Fin l.length, kfun P (l.take (j + 1))

/-- `α` for the prefix `l = [T₁,…,T_j]`: `α_j = λ_{𝒰({T₁,…,T_j})} / k(T₁,…,T_j)` (Theorem 1, p. 7). -/
def alpha (P : Params C T) (l : List T) : ℝ :=
  lamU P l.toFinset / kfun P l

/-- **Condition 1** (assignment condition, p. 4, (2)): for every sequence of distinct tokens
and every permutation of it, `∏_j λ_{T_j}({T₁,…,T_{j-1}})` is unchanged. -/
def Condition1 (P : Params C T) : Prop :=
  ∀ l l' : List T, l.Nodup → l.Perm l' → piLam P l = piLam P l'

/-- **Condition 2**, item 2 (order-independent condition, p. 5): `k(T₁,…,T_i)` is invariant
under permutations of `(T₁,…,T_i)`. (Item 1 is built into `Params.s`; item 3 and `s ≥ 0` are
part of `Params.Standing`.) -/
def Condition2 (P : Params C T) : Prop :=
  ∀ l l' : List T, l.Nodup → l.Perm l' → kfun P l = kfun P l'

/-- `k(T₁,…,T_j) > 0` for every non-empty sequence of distinct tokens (an *added* assumption:
`α_j` and the weights (10) divide by it). -/
def KPos (P : Params C T) : Prop :=
  ∀ l : List T, l.Nodup → l ≠ [] → 0 < kfun P l

/-! ### States (p. 4) -/

/-- The state space `𝒳`: a state `(T₁,n₁,…,T_i,n_i)` is the list `[(T₁,n₁),…,(T_i,n_i)]` of
token/count pairs with pairwise distinct tokens; the empty list is the empty state `(0)`. -/
abbrev State (T : Type) := {x : List (T × ℕ) // (x.map Prod.fst).Nodup}

/-- The empty state `(0)`. -/
def State.empty : State T := ⟨[], List.nodup_nil⟩

/-- The tokens `T₁,…,T_i` of a descriptor. -/
def toks (x : List (T × ℕ)) : List T := x.map Prod.fst

/-- `φ(x) = i + ∑_{j=1}^{i} n_j`, the number of customers (p. 4). -/
def phi (x : List (T × ℕ)) : ℕ := x.length + (x.map Prod.snd).sum

/-- `µ_{T_j}(x) = η(φ(x)) s_j(T₁,…,T_j)` (Condition 2, (3)): the departure rate of the active
customer holding the token at (0-based) position `j` of `x`. -/
def muTok (P : Params C T) (x : List (T × ℕ)) (j : ℕ) : ℝ :=
  P.eta (phi x) * P.s ((toks x).take (j + 1))

/-- `µ(x) = ∑_{j=1}^{i} µ_{T_j}(x)`, the total departure rate (p. 4). -/
def mu (P : Params C T) (x : List (T × ℕ)) : ℝ :=
  ∑ j ∈ range x.length, muTok P x j

/-- The weight (10) without the factor `π((0))`:
`Π_λ/Π_k · ∏_{j=1}^{i} α_j^{n_j} · ∏_{j=1}^{φ(x)} 1/η(j)`. -/
def weightL (P : Params C T) (x : List (T × ℕ)) : ℝ :=
  piLam P (toks x) / piK P (toks x) *
    (∏ j : Fin x.length, alpha P ((toks x).take (j + 1)) ^ (x.get j).2) *
    ∏ j ∈ Icc 1 (phi x), (P.eta j)⁻¹

/-- The weight (10) on the state space. -/
def weight (P : Params C T) (x : State T) : ℝ := weightL P x.1

/-! ### Forward transitions (§4.1, pp. 5–6) -/

/-- Change the count of the last portion of a descriptor by `f` (no change on `[]`). -/
def modLast (f : ℕ → ℕ) : List (T × ℕ) → List (T × ℕ)
  | [] => []
  | [(t, n)] => [(t, f n)]
  | p :: q :: l => p :: modLast f (q :: l)

/-- The departure transitions out of `y` caused by the active customer holding the token at
(0-based) position `j` (§3 p. 3, §4.1.2–4.1.3 p. 6), as a list of (target, rate) pairs.
The holder of `T_j` leaves at rate `µ_{T_j}(y)`; the token is reclaimed by the first inactive
customer behind it that is compatible with it. A customer in the portion after the token at
position `l ≥ j` is incompatible with `T_j` with probability
`b l = λ_{𝒰({T₁,…,T_l} \ {T_j})} / λ_{𝒰({T₁,…,T_l})}`, independently. If the customer that
reclaims `T_j` is the `(m+1)`-st of portion `l`, the `m` customers before it stay in front of
`T_j`; the customers of the portion of `T_j` that did not reclaim it join the previous portion.
If no customer is compatible, `T_j` is released. -/
def departures (P : Params C T) (y : List (T × ℕ)) (j : Fin y.length) :
    List (List (T × ℕ) × ℝ) :=
  let tk := toks y
  let Tj := (y.get j).1
  let jn : ℕ := j.val
  let cnt : ℕ → ℕ := fun l => (y.map Prod.snd).getD l 0
  let b : ℕ → ℝ := fun l =>
    lamU P ((tk.take (l + 1)).toFinset.erase Tj) / lamU P (tk.take (l + 1)).toFinset
  let surv : ℕ → ℝ := fun l => ∏ l' ∈ Ico jn l, b l' ^ cnt l'
  let r := muTok P y jn
  let base := modLast (· + cnt jn) (y.take jn)
  -- reclaimed by a customer of `T_j`'s own portion, after `m` incompatible ones
  ((List.range (cnt jn)).map fun m =>
      (modLast (· + m) (y.take jn) ++ (Tj, cnt jn - m - 1) :: y.drop (jn + 1),
        r * (b jn ^ m * (1 - b jn)))) ++
  -- reclaimed by a customer of the portion of the token at position `l > j`
  (((List.finRange y.length).filter (fun l => j < l)).flatMap fun (l : Fin y.length) =>
    let ln : ℕ := l.val
    (List.range (cnt ln)).map fun m =>
      (base ++ (y.take ln).drop (jn + 1) ++ ((y.get l).1, m) :: (Tj, cnt ln - m - 1) ::
          y.drop (ln + 1),
        r * (surv ln * b ln ^ m * (1 - b ln)))) ++
  -- released: no waiting customer is compatible with `T_j`
  [(base ++ y.drop (jn + 1), r * surv y.length)]

/-- All transitions out of `y` (§4.1.1–4.1.3, pp. 6), as a list of (target, rate) pairs:
an arrival that finds no compatible available token joins the end of the queue (rate
`λ_{𝒰({T₁,…,T_i})}`, only when `y ≠ (0)`); an arrival that claims the available token `t`
(rate `λ_t({T₁,…,T_i})`); and the departures of the active customers. -/
def transitions (P : Params C T) (y : List (T × ℕ)) : List (List (T × ℕ) × ℝ) :=
  let S := (toks y).toFinset
  (if y = [] then [] else [(modLast (· + 1) y, lamU P S)]) ++
  ((univ \ S).toList.map fun t => (y ++ [(t, 0)], lamTok P S t)) ++
  (List.finRange y.length).flatMap (departures P y)

/-- The transition rate `q(y, x)` from `y` to `x`: the total rate of the transitions out of `y`
that land in `x`. -/
def rate (P : Params C T) (y x : State T) : ℝ :=
  (((transitions P y.1).filter (fun e => e.1 = x.1)).map Prod.snd).sum

/-! ### The paper's backward objects (§4.1.2–4.1.4, pp. 6–7), indexed as in the paper -/

/-- `n_k` for `1 ≤ k ≤ i`, and `n_0 = 0` (p. 24). -/
def nAt (x : List (T × ℕ)) (k : ℕ) : ℕ :=
  if k = 0 then 0 else (x.map Prod.snd).getD (k - 1) 0

/-- `{T₁,…,T_k}` as a list. -/
def pre (x : List (T × ℕ)) (k : ℕ) : List T := (toks x).take k

/-- `β_k(T) = λ_{𝒰({T₁,…,T_k})} / λ_{𝒰({T₁,…,T_k,T})}` for `k ≥ 1`, and `β₀(T) = 0` ((6), p. 6). -/
def beta (P : Params C T) (x : List (T × ℕ)) (k : ℕ) (t : T) : ℝ :=
  if k = 0 then 0 else lamU P (pre x k).toFinset / lamU P (insert t (pre x k).toFinset)

/-- `release_{k,n}(x, T) = (T₁,n₁,…,T_k,n_k − n,T,n,T_{k+1},n_{k+1},…,T_i,n_i)` (p. 6). -/
def release (x : List (T × ℕ)) (k n : ℕ) (t : T) : List (T × ℕ) :=
  modLast (· - n) (x.take k) ++ (t, n) :: x.drop k

/-- `r_{k,n}(x, T) = β_k(T)^n β_{k+1}(T)^{n_{k+1}} ⋯ β_i(T)^{n_i}` (p. 6). -/
def rfac (P : Params C T) (x : List (T × ℕ)) (k n : ℕ) (t : T) : ℝ :=
  beta P x k t ^ n * ∏ l ∈ Icc (k + 1) x.length, beta P x l t ^ nAt x l

/-- `shift_{k,n}(x, T_j)` for `1 ≤ j ≤ i` and `0 ≤ k ≤ j − 1` (p. 6, **corrected**): for
`k + 1 < j` it is the printed
`(T₁,n₁,…,T_k,n_k − n,T_j,n,T_{k+1},n_{k+1},…,T_{j-1},n_{j-1}+1+n_j,T_{j+1},n_{j+1},…,T_i,n_i)`;
for `k = j − 1` it is `(T₁,n₁,…,T_{j-1},n_{j-1} − n,T_j,n+1+n_j,T_{j+1},n_{j+1},…,T_i,n_i)`.
Here `j` is the paper's (1-based) index and `Tj` is the token `T_j` of `x`. -/
def shift (x : List (T × ℕ)) (j k n : ℕ) (Tj : T) : List (T × ℕ) :=
  if k + 1 < j then
    modLast (· - n) (x.take k) ++ (Tj, n) ::
      modLast (· + (1 + nAt x j)) ((x.take (j - 1)).drop k) ++ x.drop j
  else
    modLast (· - n) (x.take k) ++ (Tj, n + 1 + nAt x j) :: x.drop j

/-- `s_{k,n}(x, T_j) = β_k(T_j)^n β_{k+1}(T_j)^{n_{k+1}} ⋯ β_{j-1}(T_j)^{n_{j-1}} (1 − β_{j-1}(T_j))`
(p. 6; for `k = j − 1` the middle product is empty). `j` is the paper's (1-based) index and
`Tj` is the token `T_j` of `x`. -/
def sfac (P : Params C T) (x : List (T × ℕ)) (j k n : ℕ) (Tj : T) : ℝ :=
  beta P x k Tj ^ n * (∏ l ∈ Icc (k + 1) (j - 1), beta P x l Tj ^ nAt x l) *
    (1 - beta P x (j - 1) Tj)

/-- Extend a function on states to all descriptors by `0` off the state space. -/
def piExt (π : State T → ℝ) (x : List (T × ℕ)) : ℝ :=
  if h : (x.map Prod.fst).Nodup then π ⟨x, h⟩ else 0

/-- The right-hand side of the global balance equations (8) (for `x ≠ (0)`) and (9) (for
`x = (0)`, where only the release terms with `k = n = 0` remain), p. 7, with the corrected
`shift`. `π` is any function on descriptors. -/
def balanceRHS (P : Params C T) (π : List (T × ℕ) → ℝ) (x : List (T × ℕ)) : ℝ :=
  let i := x.length
  let S := (toks x).toFinset
  (match x.getLast? with
   | none => 0
   | some (Ti, ni) =>
      if 0 < ni then lamU P S * π (modLast (· - 1) x)
      else lamTok P (pre x (i - 1)).toFinset Ti * π x.dropLast) +
  (∑ t ∈ univ \ S, ∑ k ∈ range (i + 1), ∑ n ∈ range (nAt x k + 1),
      muTok P (release x k n t) k * rfac P x k n t * π (release x k n t)) +
  ∑ j : Fin i, ∑ k ∈ range (j + 1), ∑ n ∈ range (nAt x k + 1),
      muTok P (shift x (j + 1) k n (x.get j).1) k * sfac P x (j + 1) k n (x.get j).1 *
        π (shift x (j + 1) k n (x.get j).1)

end

end TokenQueue.ProductForm



-- Prove2me | Definitions.Def_KellyReversibility_Networks_OpenNetwork
-- name    : KellyReversibility_Networks_OpenNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:24:15.421359+00:00
-- url     : https://prove2.me/theorems/f04f8881-f8b5-4558-8b43-2b7e3194ecb8
-- title:
--   Open network of queues with general customer routes and its transition rates (3.1)–(3.6)
-- statement:
--   This is the queueing network of Section 3.1 of Kelly's book.
--
--   **Customers and routes.** There are $I$ customer types and $J$ queues. Customers of type $i$ enter the system in a Poisson stream of rate $\nu(i)$ and visit the queues
--   $$r(i,1),\ r(i,2),\ \dots,\ r(i,S(i))$$
--   in that order before leaving the system. Two successive stages of a route are never at the same queue.
--
--   **Queues.** Queue $j$ holds its $n_j$ customers in positions $1,\dots,n_j$. Each customer needs an exponentially distributed amount of service with unit mean. Queue $j$ supplies total service effort at rate $\phi_j(n_j)$, with $\phi_j(n)>0$ for $n>0$, and a proportion $\gamma_j(l,n_j)$ of this effort goes to the customer in position $l$; when he leaves, the customers behind him move up one place. An arriving customer takes position $l\in\{1,\dots,n_j+1\}$ with probability $\delta_j(l,n_j+1)$, and the customers previously in positions $l,l+1,\dots$ move down one place. Both $\gamma_j(\cdot,n)$ and $\delta_j(\cdot,n)$ are nonnegative and sum to $1$ over the positions $1,\dots,n$.
--
--   **States.** The class $c_j(l)=(t_j(l),s_j(l))$ of the customer in position $l$ of queue $j$ is his type and the stage of his route he has reached, so $r(t_j(l),s_j(l))=j$. The state of queue $j$ is $\mathbf c_j=(c_j(1),\dots,c_j(n_j))$ and the state of the network is $\mathbf C=(\mathbf c_1,\dots,\mathbf c_J)$.
--
--   **Transition rates.** From state $\mathbf C$:
--   1. a customer in position $l$ of queue $j$ at the last stage of his route leaves the system, with probability intensity $\phi_j(n_j)\gamma_j(l,n_j)$ (3.1);
--   2. a customer in position $l$ of queue $j$ at stage $s<S(i)$ moves into position $m$ of the next queue $k=r(i,s+1)$ of his route, with intensity $\phi_j(n_j)\gamma_j(l,n_j)\delta_k(m,n_k+1)$ (3.3);
--   3. a type-$i$ customer enters the system and moves into position $m$ of queue $k=r(i,1)$, with intensity $\nu(i)\delta_k(m,n_k+1)$ (3.5).
--
--   The transition rate $q(\mathbf C,\mathbf D)$ is the sum of the intensities of all events that take $\mathbf C$ to $\mathbf D$, as in (3.2), (3.4) and (3.6): different positions can lead to the same successor state, for example when all customers of a queue are of the same class.
--
--   Two auxiliary constructions are included. The **reversed network** has the same arrival rates and effort functions, routes traversed in the opposite order, $r'(i,s)=r(i,S(i)+1-s)$, and $\gamma_j$, $\delta_j$ interchanged; a network state is relabelled as a state of the reversed network by counting each customer's stage from the other end of his route. The **arrival intensity** of type-$i$ customers at stage $s$ is, in state $\mathbf C$, the total probability intensity that a type-$i$ customer reaches queue $r(i,s)$ at stage $s$: $\nu(i)$ for $s=1$, and for $s>1$ the total intensity $\sum_l \phi_k(n_k)\gamma_k(l,n_k)$ over the positions $l$ of queue $k=r(i,s-1)$ holding a type-$i$ customer at stage $s-1$ (times $\sum_m\delta_{r(i,s)}(m,n+1)=1$).
--
--   This is the model behind Theorems 3.1 and 3.2 and Corollaries 3.4 and 3.5.
--
--   **Formalization Note** Types and queues are `Fin I` and `Fin J` (the book allows countably many types with $\sum_i\nu(i)<\infty$; this formalization takes finitely many). Stages and positions are $0$-based in Lean: the book's stage $s$ is `s - 1 : Fin (S i)` and position $l$ is list index $l-1$, while $\gamma_j(l,n)$ and $\delta_j(l,n)$ keep the book's $1$-based arguments. The book's constraints are collected in `Network.IsValid`; arrival rates are required to be positive, since a type with $\nu(i)=0$ never appears. No event leaves a state unchanged, so $q(\mathbf C,\mathbf C)=0$ is built in.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 57–61, §3.1, Eqs. (3.1)–(3.6) and the reversed process p. 61–62

import Mathlib

namespace KellyReversibility.Networks

/-- The data of an open network of queues with general customer routes (Kelly 1979, §3.1,
pp. 57–60). There are `I` customer types and `J` queues; positions in a queue and stages of a
route are counted in Lean from `0`, so the book's stage `s` is `s - 1 : Fin (S i)` and the book's
position `l` is the list index `l - 1`. The functions `γ j l n` and `δ j l n` are indexed as in the
book: position `l ∈ {1, …, n}` in a queue holding `n` customers. -/
structure Network (I J : ℕ) where
  /-- arrival rate `ν(i)` of the Poisson stream of type-`i` customers -/
  ν : Fin I → ℝ
  /-- number of stages `S(i)` of the route of a type-`i` customer -/
  S : Fin I → ℕ
  /-- the queue `r(i, s)` visited at stage `s` (stages `0, …, S(i) - 1` in Lean) -/
  r : (i : Fin I) → Fin (S i) → Fin J
  /-- total service effort `φ_j(n)` supplied at queue `j` when it holds `n` customers -/
  φ : Fin J → ℕ → ℝ
  /-- proportion `γ_j(l, n)` of the effort directed to position `l` (book indexing, `1 ≤ l ≤ n`) -/
  γ : Fin J → ℕ → ℕ → ℝ
  /-- probability `δ_j(l, n)` that an arrival making the queue length `n` takes position `l` -/
  δ : Fin J → ℕ → ℕ → ℝ

namespace Network

variable {I J : ℕ}

/-- The constraints the book places on the data (§3.1, pp. 57–59): positive arrival rates,
routes of at least one stage, no two successive stages at the same queue, `φ_j(n) > 0` for
`n > 0`, and `γ_j(·, n)`, `δ_j(·, n)` probability vectors on the positions `1, …, n`. -/
structure IsValid (N : Network I J) : Prop where
  ν_pos : ∀ i, 0 < N.ν i
  S_pos : ∀ i, 0 < N.S i
  r_succ_ne : ∀ (i : Fin I) (s : ℕ) (h : s + 1 < N.S i),
    N.r i ⟨s, Nat.lt_of_succ_lt h⟩ ≠ N.r i ⟨s + 1, h⟩
  φ_pos : ∀ j n, 0 < n → 0 < N.φ j n
  γ_nonneg : ∀ j l n, 0 ≤ N.γ j l n
  δ_nonneg : ∀ j l n, 0 ≤ N.δ j l n
  γ_sum : ∀ j n, 0 < n → ∑ l ∈ Finset.Icc 1 n, N.γ j l n = 1
  δ_sum : ∀ j n, 0 < n → ∑ l ∈ Finset.Icc 1 n, N.δ j l n = 1

/-- The class `(t, s)` of a customer at queue `j`: a type `t` and a stage `s` of its route with
`r(t, s) = j`. -/
def Cls (N : Network I J) (j : Fin J) : Type :=
  {x : Σ i : Fin I, Fin (N.S i) // N.r x.1 x.2 = j}

instance (N : Network I J) (j : Fin J) : DecidableEq (N.Cls j) := by
  unfold Cls; infer_instance

/-- A state `C = (c_1, …, c_J)` of the network: for each queue `j` the list
`c_j = (c_j(1), …, c_j(n_j))` of the classes of the customers in positions `1, …, n_j`. -/
def State (N : Network I J) : Type :=
  (j : Fin J) → List (N.Cls j)

instance (N : Network I J) : DecidableEq N.State := by
  unfold State; infer_instance

/-- The state after the customer in list index `l` of queue `j` leaves queue `j`
(customers behind him move up one position). -/
def remove (N : Network I J) (C : N.State) (j : Fin J) (l : ℕ) : N.State :=
  Function.update C j ((C j).eraseIdx l)

/-- The state after a customer of class `x` joins queue `k` at list index `m`
(customers previously in positions `m, m+1, …` move down one position). -/
def insert (N : Network I J) (C : N.State) (k : Fin J) (m : ℕ) (x : N.Cls k) : N.State :=
  Function.update C k ((C k).insertIdx m x)

/-- The class of a type-`i` customer at Lean stage `s + 1`, which lies at queue `r(i, s+1)`. -/
def stageCls (N : Network I J) (i : Fin I) (s : ℕ) (h : s < N.S i) : N.Cls (N.r i ⟨s, h⟩) :=
  ⟨⟨i, ⟨s, h⟩⟩, rfl⟩

open scoped Classical in
/-- The transition rates `q(C, D)` of the network, (3.1)–(3.6) of the book. Every possible event
from `C` is enumerated with its probability intensity, and `q(C, D)` is the **sum** of the
intensities of all events leading to `D`:
* a customer in position `l + 1` of queue `j` at the last stage of his route leaves the system,
  intensity `φ_j(n_j) γ_j(l+1, n_j)` (3.1), (3.2);
* a customer in position `l + 1` of queue `j` not at his last stage moves to position `m + 1` of
  the next queue `k` of his route, intensity `φ_j(n_j) γ_j(l+1, n_j) δ_k(m+1, n_k+1)` (3.3), (3.4);
* a type-`i` customer enters the system and moves into position `m + 1` of queue `k = r(i, 1)`,
  intensity `ν(i) δ_k(m+1, n_k+1)` (3.5), (3.6). -/
noncomputable def rate (N : Network I J) (C D : N.State) : ℝ :=
  (∑ j : Fin J, ∑ l : Fin (C j).length,
    let x := (C j).get l
    let n := (C j).length
    if h : x.1.2.1 + 1 < N.S x.1.1 then
      let k := N.r x.1.1 ⟨x.1.2.1 + 1, h⟩
      ∑ m ∈ Finset.range ((C k).length + 1),
        if D = N.insert (N.remove C j l) k m (N.stageCls x.1.1 (x.1.2.1 + 1) h) then
          N.φ j n * N.γ j (l + 1) n * N.δ k (m + 1) ((C k).length + 1)
        else 0
    else
      if D = N.remove C j l then N.φ j n * N.γ j (l + 1) n else 0) +
  ∑ i : Fin I,
    if h : 0 < N.S i then
      let k := N.r i ⟨0, h⟩
      ∑ m ∈ Finset.range ((C k).length + 1),
        if D = N.insert C k m (N.stageCls i 0 h) then
          N.ν i * N.δ k (m + 1) ((C k).length + 1)
        else 0
    else 0

/-- The reversed network suggested on p. 61: customers of type `i` arrive at rate `ν(i)` and
traverse `r(i, S(i)), r(i, S(i)-1), …, r(i, 1)`; the functions `γ_j` and `δ_j` are interchanged. -/
def reverse (N : Network I J) : Network I J where
  ν := N.ν
  S := N.S
  r := fun i s => N.r i s.rev
  φ := N.φ
  γ := N.δ
  δ := N.γ

/-- A customer at stage `s` of his route in the network is at stage `S(i) + 1 - s` of the
reversed route in the reversed network (`Fin.rev` in Lean's `0`-based stages). -/
def revCls (N : Network I J) {j : Fin J} (x : N.Cls j) : N.reverse.Cls j :=
  ⟨⟨x.1.1, x.1.2.rev⟩, by
    show N.r x.1.1 x.1.2.rev.rev = j
    rw [Fin.rev_rev]; exact x.2⟩

/-- The relabelling of a network state as a state of the reversed network (each customer keeps
his type and his position; his stage is counted from the other end of his route). -/
def revState (N : Network I J) (C : N.State) : N.reverse.State :=
  fun j => (C j).map N.revCls

/-- The total probability intensity, in state `C`, that a type-`i` customer reaches the queue
`r(i, s)` of stage `s` of his route (Lean stage `s`, `0`-based): for the first stage it is the
arrival rate `ν(i)`; for a later stage it is the total intensity that a type-`i` customer at the
previous stage completes service, at any position of queue `r(i, s-1)`, and the arriving customer
takes any position of queue `r(i, s)`. -/
noncomputable def arrivalIntensity (N : Network I J) (i : Fin I) (s : Fin (N.S i))
    (C : N.State) : ℝ :=
  let j := N.r i s
  (if h : s.1 = 0 then N.ν i
   else
    let k := N.r i ⟨s.1 - 1, by omega⟩
    ∑ l : Fin (C k).length,
      if ((C k).get l).1 = ⟨i, ⟨s.1 - 1, by omega⟩⟩ then
        N.φ k (C k).length * N.γ k (l + 1) (C k).length
      else 0) *
  ∑ m ∈ Finset.Icc 1 ((C j).length + 1), N.δ j m ((C j).length + 1)

end Network

end KellyReversibility.Networks



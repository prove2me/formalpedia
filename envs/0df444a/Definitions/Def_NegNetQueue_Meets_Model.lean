-- Prove2me | Definitions.Def_NegNetQueue_Meets_Model
-- name    : NegNetQueue_Meets_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:42.260674+00:00
-- url     : https://prove2.me/theorems/fa231a14-5df3-4a44-a3e4-0031c4b5f80e
-- title:
--   §4, pp. 9–10 — the tagged customer's state, X_j, Y_j, M_j, X_{j,k}, the queue length at entry, and the matrix A of (2)
-- statement:
--   Fix the capacity $n$ of the waiting room. A **tagged customer** waits in the queue. Her state records four natural numbers: her **position** (position $j$ means $j-1$ customers wait ahead of her; position $0$ means she has entered service), the **queue length** (the number of waiting customers, herself included, not counting those in service), the number of **later arrivals met** (arrivals after her that joined the queue), and the number of those that **filled the queue** (arrived to position $n$).
--
--   One event updates the state as follows. If she is already in service, nothing changes. A service completion moves everybody up: position and queue length both decrease by one. An arrival that finds the queue length below $n$ joins: the queue length and the number met increase by one, and if the new queue length is $n$ the queue-filling count increases by one as well. An arrival that finds $n$ waiting customers is lost and changes nothing. Running the events of a sequence one after another gives the state after $t$ events.
--
--   From the start "position $j$, queue length $j$" (a customer who has just arrived at position $j$):
--   1. $X_j$ is the final number of later arrivals met, the supremum over $t$ of the count after $t$ events;
--   2. $Y_j$ is the final number among them that filled the queue;
--   3. $M_j=j-1+X_j$ is the total number of waiting customers met.
--
--   From the start "position $j$, queue length $k$" ($k\ge j$), $X_{j,k}$ is the final number of additional customers met, and the **queue length at entry** is the queue length at the moment her position reaches $0$ (it is $0$ on the null event that she never enters service).
--
--   The matrix $A$ of (2) is the $(n+1)\times(n+1)$ matrix, indexed by queue sizes $0,\dots,n$, with
--   $$A(k,i)=\begin{cases} q(1-q)^{i-k+1} & 0<k<n,\ k-1\le i<n-1,\\ (1-q)^{n-k} & 0<k<n,\ i=n-1,\\ 1 & k=n,\ i=n-1, \text{ or } k=i=0,\\ 0 & \text{otherwise}.\end{cases}$$
--   Its row $k$ is meant to be the law of the queue size at the next service completion, starting from queue size $k$.
--
--   **Formalization Note.** The counts are valued in $\mathbb N\cup\{\infty\}$ and defined as eventual values (suprema of non-decreasing sequences), so no default value enters. The third case of (2) on the page reads "$j=n, k=n-1$ or $j=k=0$", with $k$ standing for the column index $i$; the matrix is built that way, in agreement with the prose before (2) ("state $n$ transits to $n-1$ with probability 1", "the absorbing state 0"). Exponents are natural numbers; on the range $k-1\le i$ the exponent $i+1-k$ involves no truncation. $A$ is defined for any real $q$; the theorems use $q=c\mu/(\lambda+c\mu)$.
-- source:
--   Hassin, Meilijson & Perlman, Queueing with Negative Network Effects, SSRN 4097977 (version of July 2, 2022), pp. 9–10, §4: M_j = j − 1 + X_j and X_j (p. 9), display (2) and the prose before it (p. 9), Theorem 2 (2) and Y_j in Theorem 3 (p. 10)

import Mathlib

namespace NegNetQueue.Meets

/-- The state of a tagged customer waiting in an M/M/c/n queue: her position `pos` in the queue
(`pos = j` means `j - 1` customers wait ahead of her; `pos = 0` means she has entered service),
the queue length `len` (waiting customers, her included), the number `met` of later arrivals that
joined the queue, and the number `fill` of those that arrived to position `n`. -/
structure TagState where
  pos : ℕ
  len : ℕ
  met : ℕ
  fill : ℕ

/-- One event of the queue with waiting room `n`: `true` is a service completion, `false` an
arrival. Once the tagged customer is in service (`pos = 0`) the state is frozen. A completion moves
everybody up one place. An arrival joins (and is met) if `len < n`, and fills the queue if it
arrives to position `n`; an arrival finding `len = n` is lost. -/
def step (n : ℕ) (s : TagState) (e : Bool) : TagState :=
  if s.pos = 0 then s
  else if e then { s with pos := s.pos - 1, len := s.len - 1 }
  else if s.len < n then
    { s with len := s.len + 1, met := s.met + 1,
             fill := s.fill + if s.len + 1 = n then 1 else 0 }
  else s

/-- The state after `t` events of the sequence `ev`, started from `s₀`. -/
def run (n : ℕ) (s₀ : TagState) (ev : ℕ → Bool) : ℕ → TagState
  | 0 => s₀
  | t + 1 => step n (run n s₀ ev t) (ev t)

/-- `X_j` (§4, p. 9): the number of later arrivals met (that join the queue) before a customer
arriving at position `j` of the queue with capacity `n` enters service. -/
noncomputable def Xmet {Ω : Type*} (n j : ℕ) (ε : ℕ → Ω → Bool) (ω : Ω) : ℕ∞ :=
  ⨆ t, ((run n ⟨j, j, 0, 0⟩ (fun t => ε t ω) t).met : ℕ∞)

/-- `X_{j,k}` (Theorem 2 (2), p. 10): the number of additional customers met (later arrivals that
join the queue) before a customer in position `j` of a queue of current length `k` enters service.
`X_j = X_{j,j}`. -/
noncomputable def XmetAt {Ω : Type*} (n j k : ℕ) (ε : ℕ → Ω → Bool) (ω : Ω) : ℕ∞ :=
  ⨆ t, ((run n ⟨j, k, 0, 0⟩ (fun t => ε t ω) t).met : ℕ∞)

/-- `Y_j` (Theorem 3, p. 10): the number among these `X_j` customers who fill up the queue (arrive
to position `n`). -/
noncomputable def Yfill {Ω : Type*} (n j : ℕ) (ε : ℕ → Ω → Bool) (ω : Ω) : ℕ∞ :=
  ⨆ t, ((run n ⟨j, j, 0, 0⟩ (fun t => ε t ω) t).fill : ℕ∞)

/-- `M_j = j - 1 + X_j` (§4, p. 9): the total number of waiting customers met. -/
noncomputable def Mmeet {Ω : Type*} (n j : ℕ) (ε : ℕ → Ω → Bool) (ω : Ω) : ℕ∞ :=
  ((j - 1 : ℕ) : ℕ∞) + Xmet n j ε ω

/-- The queue length at the moment a customer in position `j` of a queue of current length `k`
enters service (the frozen value of `len` once `pos = 0`; `0` if she never enters service). -/
noncomputable def lenAtEntry {Ω : Type*} (n j k : ℕ) (ε : ℕ → Ω → Bool) (ω : Ω) : ℕ∞ :=
  ⨆ t, (if (run n ⟨j, k, 0, 0⟩ (fun t => ε t ω) t).pos = 0 then
          ((run n ⟨j, k, 0, 0⟩ (fun t => ε t ω) t).len : ℕ∞) else 0)

/-- The matrix `A` of (2), p. 9: the transition matrix of the queue size at consecutive service
completions, with `q` the probability that the next change is a service completion. Row `0` is
absorbing, row `n` moves to `n - 1`, and for `0 < k < n` row `k` puts `q (1-q)^{i-k+1}` on
`k - 1 ≤ i ≤ n - 2` and `(1-q)^{n-k}` on `i = n - 1`. -/
noncomputable def Amat (n : ℕ) (q : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun a b =>
  if (a : ℕ) = 0 then (if (b : ℕ) = 0 then 1 else 0)
  else if (a : ℕ) = n then (if (b : ℕ) = n - 1 then 1 else 0)
  else if (a : ℕ) - 1 ≤ (b : ℕ) ∧ (b : ℕ) < n - 1 then q * (1 - q) ^ ((b : ℕ) + 1 - (a : ℕ))
  else if (b : ℕ) = n - 1 then (1 - q) ^ (n - (a : ℕ))
  else 0

end NegNetQueue.Meets



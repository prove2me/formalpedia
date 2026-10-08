-- Prove2me | Definitions.Def_PacketRouting_CongDil_Timetable
-- name    : PacketRouting_CongDil_Timetable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:44:23.210295+00:00
-- url     : https://prove2.me/theorems/09868c3c-60a8-46f5-ac4e-d161819f4287
-- title:
--   §1, p. 2; §3, pp. 8, 13 — schedules as timetables, edge exclusivity, edge queues, frames and relative congestion
-- statement:
--   This module fixes what a **schedule** is (p. 2: "A schedule for a set of packets specifies which move and which wait at each time step") and the quantities the paper measures on it.
--
--   Time steps are numbered $1,2,3,\dots$. A schedule (a **timetable**) assigns to every packet $p$ and every index $0\le k<|\mathrm{path}(p)|$ the step $\tau(p,k)\ge 1$ at which $p$ traverses the $k$-th edge of its path, with
--   $$
--   \tau(p,0)<\tau(p,1)<\dots<\tau(p,|\mathrm{path}(p)|-1).
--   $$
--   So every packet crosses every edge of its path, in path order, at most one edge per step; before its first crossing it waits in its initial queue, between two crossings it waits in the edge queue at the head of the edge it last crossed, and after its last crossing it sits in its final queue. On top of this:
--
--   1. **Valid** (Theorem 3.4): at most one packet traverses each edge at each step, i.e. two different crossings $(p,k)\ne(q,l)$ of the same edge happen at different steps. The intermediate schedules of the paper need not be valid.
--   2. **Length at most $L$**: every crossing happens at a step $\le L$.
--   3. **No edge waits** (Lemma 3.2): $\tau(p,k+1)=\tau(p,k)+1$ for every $k$; a packet waits only in its initial queue.
--   4. **Edge-queue size** of an edge $g$ at the end of step $t$: the number of crossings $(p,k)$ of $g$ with $\tau(p,k)\le t<\tau(p,k+1)$, where $k$ is not the last index of $p$'s path. Initial and final queues are not counted (p. 2: "any bound on the maximum queue size required by a routing algorithm refers only to the edge queues").
--   5. **Frames** (p. 8): a $T$-frame is a sequence of $T$ consecutive steps $t,t+1,\dots,t+T-1$. A packet *uses* $g$ in the frame if it crosses $g$ at a step of the frame; $C_g(t,T)$ is the number of such packets. The **relative congestion is at most $r$ in every frame of size $T_0$ or greater** if $C_g(t,T)\le rT$ for every edge $g$, every start $t$, and every $T\ge 1$ with $T\ge T_0$.
--   6. **Waiting at most once every $k_1$ steps** (p. 13): a packet waits at step $s$ if $s$ lies strictly between its crossings of two consecutive edges; the condition says that in any $k_1$ consecutive steps every packet waits at most once.
--
--   These are the objects of the main theorem (a valid schedule of length $O(c+d)$ with bounded edge queues) and of the refinement argument (schedules with bounded relative congestion in large frames).
--
--   **Formalization Note** The edge-queue count is taken at the end of a step; counting at the beginning of a step changes it by at most one packet. Relative congestion is stated without division, as $C_g(t,T)\le rT$, with a real threshold $T_0$ so that it can be $\log_2 d$.
-- source:
--   Leighton, Maggs & Rao, Packet routing and job-shop scheduling in O(congestion + dilation) steps, authors' manuscript (preprint of Combinatorica 14 (1994), DOI 10.1007/BF01215349), p. 2 (queues, schedule), p. 8 (T-frame, frame congestion, relative congestion), p. 11 Theorem 3.4 (one packet per edge per step), p. 13 (waiting invariant)

import Mathlib

namespace PacketRouting.CongDil

/-- A **schedule** (Leighton–Maggs–Rao, p. 2: "A schedule for a set of packets specifies which
move and which wait at each time step"), in timetable form. Time steps are numbered `1, 2, 3, …`.
For every packet `p` and every index `k < length (path p)`, `time p k` is the step at which `p`
traverses the `k`-th edge of its path. Every packet traverses every edge of its path, in path
order, at most one edge per step (`time p` is strictly increasing). Between two traversals the
packet waits in the edge queue of the edge it last traversed; before its first traversal it waits
in its initial queue. A timetable alone does **not** require that at most one packet traverses
an edge at a step (that is `Timetable.Valid`): the intermediate schedules `S₀, S₁, …, S_j` of
the paper violate it. -/
structure Timetable {P E : Type*} (path : P → List E) where
  /-- `time p k`: the step at which packet `p` traverses the `k`-th edge of its path. -/
  time : (p : P) → Fin (path p).length → ℕ
  /-- Steps are numbered from `1`. -/
  one_le_time : ∀ p k, 1 ≤ time p k
  /-- Edges are traversed in path order, one per step at most. -/
  strictMono_time : ∀ p, StrictMono (time p)

namespace Timetable

variable {P E : Type*} {path : P → List E}

/-- **At most one packet traverses each edge of the network at each step** (Theorem 3.4,
p. 11): two distinct traversals `(p, k) ≠ (q, l)` of the same edge happen at different steps. -/
def Valid (τ : Timetable path) : Prop :=
  ∀ (p q : P) (k : Fin (path p).length) (l : Fin (path q).length),
    (path p).get k = (path q).get l → τ.time p k = τ.time q l → p = q ∧ k.val = l.val

/-- The schedule has **length at most `L`**: every traversal happens at one of the steps
`1, …, L`. -/
def LengthLE (τ : Timetable path) (L : ℕ) : Prop :=
  ∀ p k, τ.time p k ≤ L

/-- **Packets never wait in edge queues** (Lemma 3.2, p. 8): after its first traversal a packet
traverses the next edge of its path at every following step until it reaches its destination;
it waits only in its initial queue. -/
def NoEdgeWait (τ : Timetable path) : Prop :=
  ∀ (p : P) (k : ℕ) (h : k + 1 < (path p).length),
    τ.time p ⟨k + 1, h⟩ = τ.time p ⟨k, Nat.lt_of_succ_lt h⟩ + 1

/-- The number of packets in the **edge queue of edge `g` at the end of step `t`** (p. 2:
"When a packet traverses an edge, it enters the edge queue at the end of that edge"; "Upon
traversing the last edge on its path, a packet is removed from the edge queue and placed in a
special final queue"). It counts the traversals `(p, k)` of `g` that happened at a step `≤ t`
and for which `p` has a next edge, traversed at a step `> t`. Packets in initial queues (not yet
moved) and in final queues (after their last edge) are not counted (p. 2: "any bound on the
maximum queue size … refers only to the edge queues"). -/
noncomputable def queueSize [Fintype P] (τ : Timetable path) (g : E) (t : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : (Σ p : P, Fin (path p).length) =>
    (path x.1).get x.2 = g ∧ τ.time x.1 x.2 ≤ t ∧
      ∃ h : x.2.val + 1 < (path x.1).length, t < τ.time x.1 ⟨x.2.val + 1, h⟩)).card

/-- The number of packets that **use edge `g` in the `T`-frame starting at step `t`** (p. 8: "A
`T`-frame is a sequence of `T` consecutive time steps"), i.e. the packets that traverse `g` at
some step `s` with `t ≤ s < t + T`. This is the quantity whose maximum over edges is the frame
congestion `C`; the relative congestion of the frame is `C / T`. -/
noncomputable def frameCount [Fintype P] (τ : Timetable path) (g : E) (t T : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : P =>
    ∃ k : Fin (path p).length, (path p).get k = g ∧ t ≤ τ.time p k ∧ τ.time p k < t + T)).card

/-- **Relative congestion at most `r` in every frame of size `T₀` or greater** (p. 8): for every
edge `g`, every frame size `T ≥ 1` with `T₀ ≤ T`, and every starting step `t`, at most `r · T`
packets use `g` in the `T`-frame starting at `t`. The threshold `T₀` is real so that it can be
`log d`. -/
def RelCongLE [Fintype P] (τ : Timetable path) (r T₀ : ℝ) : Prop :=
  ∀ (g : E) (t T : ℕ), 1 ≤ T → T₀ ≤ (T : ℝ) → (τ.frameCount g t T : ℝ) ≤ r * T

/-- Packet `p` **waits at step `s`** in an edge queue: `s` lies strictly between the steps at
which `p` traverses two consecutive edges of its path. -/
def WaitsAt (τ : Timetable path) (p : P) (s : ℕ) : Prop :=
  ∃ (k : ℕ) (h : k + 1 < (path p).length),
    τ.time p ⟨k, Nat.lt_of_succ_lt h⟩ < s ∧ s < τ.time p ⟨k + 1, h⟩

/-- **Every packet waits at most once every `k₁` steps** (p. 13): in any `k₁` consecutive steps
each packet waits in an edge queue at most once. -/
def WaitsAtMostOnceEvery (τ : Timetable path) (k₁ : ℕ) : Prop := by
  classical
  exact ∀ (p : P) (t : ℕ),
    ((Finset.Ico t (t + k₁)).filter (fun s => τ.WaitsAt p s)).card ≤ 1

end Timetable

end PacketRouting.CongDil



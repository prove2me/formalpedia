-- Prove2me | Definitions.Def_RGMISFast_tau
-- name    : RGMISFast_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:43.307231+00:00
-- url     : https://prove2.me/theorems/e8eb2a78-048c-48d7-8a47-a5b5eaed5fc1
-- title:
--   Greedy MIS $I$, settling time $\tau(v)=\min\{r(x):x\in I\cap N^+[v]\}$ and activity
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with ranks $r$. The **greedy independent set** $I$ is defined by recursion on the rank: a vertex $v$ belongs to $I$ exactly when none of its neighbours of smaller rank belongs to $I$ (the sequential greedy algorithm processes vertices in increasing order of rank and selects each vertex not yet settled).
--
--   The **settling time** of $v$ is
--   $$
--   \tau(v)=\min\{\,r(x): x\in I\cap N^+[v]\,\},
--   $$
--   the rank of the first selected vertex in the closed neighbourhood $N^+[v]=\{v\}\cup N(v)$. The set $I\cap N^+[v]$ is never empty: either $v\in I$, or some neighbour of smaller rank lies in $I$. A vertex $v$ is **active at time $t$** if $t\le\tau(v)$ and settled at time $t$ if $t>\tau(v)$; a vertex set $A$ is active at time $t$ if all its vertices are. The **active graph** $G_t$ is the subgraph induced by the vertices active at $t$.
--
--   Settling times and activity drive every probabilistic estimate of the mission.
--
--   **Formalization Note** $I$ is given by the rank recursion; that the answers of Procedure 1.1 coincide with it is part of Observation 2.2. The minimum is taken over a finite set proved nonempty in the module, so $\tau$ never takes a default value.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), §2, p.10 (PDF p.12), Definition 2.1, eq. (4); activity and G_t, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_RGMISFast_run

set_option autoImplicit false

namespace RGMISFast

/-- Membership in the greedy independent set by the rank recursion, with a bound `n` on the
termination measure (helper for `inMIS`; the case `n = 0` is impossible). -/
def inMISF {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [LinearOrder α] (r : V → α) : (n : ℕ) → (v : V) → rk r v < n → Bool
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, v, h => (lowerNbrs G r v).attach.all (fun w =>
      !inMISF G r n w.1 (by have := rk_lt r ((mem_lowerNbrs G r).1 w.2).2; omega))

theorem inMISF_irrel {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {α : Type*} [LinearOrder α] (r : V → α) :
    ∀ (n m : ℕ) (v : V) (h : rk r v < n) (h' : rk r v < m),
      inMISF G r n v h = inMISF G r m v h'
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h' => absurd h' (Nat.not_lt_zero _)
  | n + 1, m + 1, v, h, h' => by
    simp only [inMISF]
    congr 1
    funext w
    rw [inMISF_irrel G r n m w.1]

/-- The greedy maximal independent set `I` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran,
*Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256
e93cdfec…), §2, p.10): "A vertex is selected exactly when none of its neighbors of lower rank are
selected, as in the recursive procedure. Hence, by induction on the rank, the set of vertices
selected by the sequential algorithm is exactly the set I from Section 1.1." `inMIS G r v = true`
iff `v ∈ I`.

**Formalization Note** `I` is defined by this recursion on the rank (a vertex is in `I` iff no
neighbour of strictly smaller rank is in `I`). That the answers of Procedure 1.1 agree with it is
clause (0) of Observation 2.2, a milestone. -/
def inMIS {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [LinearOrder α] (r : V → α) (v : V) : Bool :=
  inMISF G r (rk r v + 1) v (Nat.lt_succ_self _)

theorem inMIS_eq {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {α : Type*} [LinearOrder α] (r : V → α) (v : V) :
    inMIS G r v = (lowerNbrs G r v).attach.all (fun w => !inMIS G r w.1) := by
  conv_lhs => unfold inMIS; rw [inMISF]
  congr 1
  funext w
  unfold inMIS
  rw [inMISF_irrel G r _ (rk r w.1 + 1) w.1]

/-- The closed neighbourhood `N⁺[v]` always meets `I`: either `v ∈ I`, or some neighbour of
smaller rank is in `I`. -/
theorem tauSet_nonempty {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {α : Type*} [LinearOrder α] (r : V → α) (v : V) :
    ((insert v (G.neighborFinset v)).filter (fun x => inMIS G r x = true)).Nonempty := by
  cases hv : inMIS G r v with
  | true => exact ⟨v, by simp [hv]⟩
  | false =>
    have h := inMIS_eq G r v
    rw [hv] at h
    obtain ⟨w, -, hw⟩ := List.all_eq_false.1 h.symm
    have hadj := ((mem_lowerNbrs G r).1 w.2).1
    refine ⟨w.1, ?_⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hw
    simp only [Finset.mem_filter, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
    cases h' : inMIS G r w.1 <;> simp_all

/-- The settling time `τ(v)` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized
Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…),
Definition 2.1, eq. (4), p.10): `τ(v) = min{r(x) : x ∈ I ∩ N⁺[v]}`, the rank of the first
selected vertex in the closed neighbourhood of `v`.

**Formalization Note** The minimum is `Finset.min'` over the image under `r` of the finite set
`I ∩ N⁺[v]`, which is nonempty for every `v` (`tauSet_nonempty`); no junk value is involved. -/
def tau {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [LinearOrder α] (r : V → α) (v : V) : α :=
  (((insert v (G.neighborFinset v)).filter (fun x => inMIS G r x = true)).image r).min'
    ((tauSet_nonempty G r v).image r)

/-- A vertex set `A` is active at time `t` if every vertex of `A` is active at `t`, i.e.
`t ≤ τ(v)` for all `v ∈ A` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized
Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §2,
p.11). Equivalently `A ⊆ V(G_t)`, where the active graph `G_t` is the subgraph induced by the
vertices `v` with `t ≤ τ(v)`.

**Formalization Note** Activity is the closed condition `t ≤ τ(v)`; a vertex is settled at `t`
when `t > τ(v)`. -/
def ActiveAt {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [LinearOrder α] (r : V → α) (t : α) (A : Finset V) : Prop :=
  ∀ v ∈ A, t ≤ tau G r v

instance {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {α : Type*} [LinearOrder α] (r : V → α) (t : α) (A : Finset V) :
    Decidable (ActiveAt G r t A) :=
  inferInstanceAs (Decidable (∀ v ∈ A, t ≤ tau G r v))

end RGMISFast



-- Prove2me | Definitions.Def_ExAnteExPost_RPS_Model
-- name    : ExAnteExPost_RPS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:02.124131+00:00
-- url     : https://prove2.me/theorems/0c0f40cc-c45f-47ce-ab8e-afe2d9bbb798
-- title:
--   §2–§3.1, pp. 4–10 — allocations, EF, EF1, randomized allocations, the eating protocol, Theorem 1 decompositions and Algorithm 1 (Recursive Probabilistic Serial)
-- statement:
--   This file fixes the model of Freeman, Shah and Vaish's *Best of Both Worlds* (§2 and §3.1) and defines Recursive Probabilistic Serial (Algorithm 1).
--
--   **Instances.** There is a finite set $N$ of $n$ agents and a finite set $M$ of $m$ goods (the whole type of goods). Agent $i$ has an additive valuation with values $v_{i,g} \ge 0$ for fully receiving good $g$.
--
--   **Allocations.** A *fractional allocation* is a matrix $X = (X_{i,g})$, where $X_{i,g}$ is the fraction of good $g$ given to agent $i$. An *integral allocation* is written in set notation: $A_i \subseteq M$ is agent $i$'s bundle, and its $0/1$ matrix has $A_{i,g} = 1$ exactly when $g \in A_i$. It is *proper* when the bundles of distinct agents are disjoint. Agent $i$'s value for a row $x$ is $v_i(x) = \sum_{g} x_g v_{i,g}$, and for a bundle $S$ it is $v_i(S) = \sum_{g \in S} v_{i,g}$.
--
--   **Fairness.** $X$ is *envy-free* (Definition 3) if $v_i(X_i) \ge v_i(X_h)$ for all agents $i, h$. An integral allocation $A$ is *envy-free up to one good* (EF1, Definition 8) if for all $i, h$ with $A_h \ne \emptyset$ there is a good $j \in A_h$ with $v_i(A_i) \ge v_i(A_h \setminus \{j\})$.
--
--   **Randomized allocations.** A randomized allocation is a finite list of pairs $(p^k, A^k)$ of a probability and an integral allocation; it is well formed when every $p^k \in [0,1]$, every $A^k$ is proper and $\sum_k p^k = 1$. It *implements* the fractional allocation $\sum_k p^k A^k$. It is *ex-ante envy-free* if that fractional allocation is envy-free, and *ex-post EF1* if every $A^k$ with $p^k > 0$ is EF1.
--
--   **Theorem 1 decompositions.** A matrix satisfies the *hypotheses of Theorem 1* if its entries lie in $[0,1]$ and all its row and column sums are at most $1$. A *decomposition* of $X$ is a finite family of weights $w^1, \dots, w^q$ and integral allocations $A^1, \dots, A^q$ satisfying the conclusions of Theorem 1: $w^k \in [0,1]$, $\sum_k w^k = 1$, $X = \sum_k w^k A^k$, and for every $k$
--   $$\Big\lfloor \sum_{g} X_{i,g} \Big\rfloor \le |A^k_i| \le \Big\lceil \sum_{g} X_{i,g} \Big\rceil, \qquad \Big\lfloor \sum_{i} X_{i,g} \Big\rfloor \le |\{i : g \in A^k_i\}| \le \Big\lceil \sum_{i} X_{i,g} \Big\rceil .$$
--   A *decomposition rule* $D$ is admissible if $D(X)$ is such a decomposition of every matrix $X$ satisfying the hypotheses of Theorem 1.
--
--   **The eating protocol.** A *choice rule* assigns to each agent $i$ and each nonempty set $S$ of goods a good of $S$; it is a *favorite-good rule* if that good has maximal value $v_{i,\cdot}$ in $S$, with ties broken arbitrarily. $\mathrm{Eating}(M', 1)$ runs the eating protocol on the goods $M'$ for one unit of time: every good of $M'$ starts with mass one, and at every moment each agent eats, at rate one, the good her choice rule selects among the goods not yet fully consumed. The protocol is computed event by event: between two events every agent eats a fixed good, and the next event occurs when the remaining time runs out or when a good being eaten is exhausted, whichever is first. At most $|M| + 1$ events occur in one unit of time.
--
--   **Algorithm 1.** One stage on the goods $M^t$ computes $X^t = \mathrm{Eating}(M^t, 1)$, decomposes $X^t = \sum_k w^{t,k} A^{t,k}$ with the rule $D$, samples $B^t = A^{t,k}$ with probability $w^{t,k}$, and continues on $M^{t+1} = M^t \setminus \bigcup_i B^t_i$. Running $T$ stages from $M'$ gives a list of stage histories $(B^1, \dots, B^T)$, each with probability the product of its sampled weights, and the final allocation $B_i = \bigcup_t B^t_i$. Algorithm 1 runs $\lceil m/n \rceil$ stages from $M^1 = M$.
--
--   This vocabulary is used by every statement of the mission: the goal (Theorem 2) and its milestones speak about the eating protocol and the lottery that Algorithm 1 computes, not about free variables.
--
--   **Formalization Note.** Agents and goods are finite types with decidable equality, and the number of stages is $\lceil m/n \rceil$ computed in $\mathbb R$ (so $n \ge 1$ is required where Algorithm 1 is used). The paper's standing assumption that every good is valued positively by some agent is a without-loss-of-generality convention that the proof does not use; it is omitted. Algorithm 1's printed line 2 initializes $M^0$ while the loop starts at $M^1$, and its line 8 unions over all stages inside the loop; the definition implements the intended algorithm, $M^1 = M$ and $B_i = \bigcup_t B^t_i$, which agrees with the recursive Algorithm 3 (Appendix D) and with the proof of Theorem 2. Conclusion 2 of Theorem 1 ($0/1$ entries) is built into integral allocations being bundles. A choice rule only has to choose on nonempty sets, so a favorite-good rule exists for every instance, including one with no goods.
-- source:
--   Freeman, Shah, Vaish, Best of Both Worlds: Ex-Ante and Ex-Post Fairness in Resource Allocation, arXiv:2005.14122v1, pp. 4–10 and 33, §2, Definitions 3 and 8, §2.1 (ex-ante, ex-post), §3.1 (eating protocol, Theorem 1, Algorithm 1), Appendix D (Algorithm 3)

import Mathlib

namespace ExAnteExPost.RPS
open Finset

/-- A fair-division instance with agents `N` and goods `G` (§2, pp. 4–5): agent `i` has an additive
valuation with value `v i g ≥ 0` for fully receiving good `g`. -/
structure Instance (N G : Type*) where
  v : N → G → ℝ
  nonneg : ∀ i g, 0 ≤ v i g

/-- A fractional allocation: `X i g` is the fraction of good `g` assigned to agent `i` (p. 4). -/
abbrev FracAlloc (N G : Type*) := N → G → ℝ

/-- An integral allocation in the paper's set notation: `A i` is the bundle of agent `i` (p. 4). -/
abbrev IntAlloc (N G : Type*) := N → Finset G

/-- A finite randomized allocation: a list of pairs (probability, integral allocation) (p. 5). -/
abbrev Lottery (N G : Type*) := List (ℝ × IntAlloc N G)

/-- One integral decomposition `X = ∑ₖ wᵏ Aᵏ` with `q` terms, as produced by Theorem 1 (p. 9). -/
structure Decomp (N G : Type*) where
  q : ℕ
  w : Fin q → ℝ
  A : Fin q → IntAlloc N G

/-- A choice rule for the eating protocol: `pick i S hS` is the good agent `i` eats when the goods
of the nonempty set `S` are available. -/
abbrev PickRule (N G : Type*) := N → (S : Finset G) → S.Nonempty → G

/-- State of the eating protocol between two events: unconsumed mass of each good, the fractional
allocation consumed so far, and the eating time left. -/
structure EatState (N G : Type*) where
  rem : G → ℝ
  X : FracAlloc N G
  τ : ℝ

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- The 0/1 matrix of an integral allocation. -/
def toFrac (A : IntAlloc N G) : FracAlloc N G := fun i g => if g ∈ A i then 1 else 0

/-- Bundles of distinct agents are disjoint (each good goes to at most one agent). -/
def IsIntAlloc (A : IntAlloc N G) : Prop := ∀ i h, i ≠ h → Disjoint (A i) (A h)

/-- `v_i(x) = ∑_g x_g v_{i,g}` for a row `x` of a fractional allocation (p. 5). -/
def util (I : Instance N G) (i : N) (x : G → ℝ) : ℝ := ∑ g, x g * I.v i g

/-- Definition 3 (EF): `v_i(X_i) ≥ v_i(X_h)` for all agents `i, h`. -/
def IsEF (I : Instance N G) (X : FracAlloc N G) : Prop := ∀ i h, util I i (X h) ≤ util I i (X i)

/-- Definition 8 (EF1): for all `i, h` with `A_h ≠ ∅` there is `j ∈ A_h` with
`v_i(A_i) ≥ v_i(A_h \ {j})`. -/
def IsEF1 (I : Instance N G) (A : IntAlloc N G) : Prop :=
  ∀ i h, (A h).Nonempty → ∃ j ∈ A h, ∑ g ∈ (A h).erase j, I.v i g ≤ ∑ g ∈ A i, I.v i g

/-- A randomized allocation (p. 5): probabilities in `[0,1]` summing to one, integral allocations. -/
def IsRandAlloc (L : Lottery N G) : Prop :=
  (∀ e ∈ L, 0 ≤ e.1 ∧ e.1 ≤ 1 ∧ IsIntAlloc e.2) ∧ (L.map Prod.fst).sum = 1

/-- The fractional allocation `∑ₖ pᵏ Aᵏ` that a randomized allocation implements (p. 5). -/
def implements (L : Lottery N G) : FracAlloc N G :=
  fun i g => (L.map fun e => e.1 * toFrac e.2 i g).sum

/-- Ex-ante EF: the implemented fractional allocation is envy-free (p. 5). -/
def ExAnteEF (I : Instance N G) (L : Lottery N G) : Prop := IsEF I (implements L)

/-- Ex-post EF1: every integral allocation drawn with positive probability is EF1 (p. 5). -/
def ExPostEF1 (I : Instance N G) (L : Lottery N G) : Prop := ∀ e ∈ L, 0 < e.1 → IsEF1 I e.2

/-- Hypotheses 1–3 of Theorem 1 (p. 9): entries in `[0,1]`, row sums and column sums at most one. -/
def BvNInput (X : FracAlloc N G) : Prop :=
  (∀ i g, 0 ≤ X i g ∧ X i g ≤ 1) ∧ (∀ i, ∑ g, X i g ≤ 1) ∧ ∀ g, ∑ i, X i g ≤ 1

/-- The agents holding good `g` in `A` (the column sum of the 0/1 matrix of `A`). -/
def holders (A : IntAlloc N G) (g : G) : Finset N := univ.filter fun i => g ∈ A i

/-- Conclusions 1–3 of Theorem 1 (p. 9) for the decomposition `d` of `X`; conclusion 2 (0/1 entries)
is built into `IntAlloc`. -/
def IsBvNDecomp (X : FracAlloc N G) (d : Decomp N G) : Prop :=
  (∀ k, 0 ≤ d.w k ∧ d.w k ≤ 1) ∧ ∑ k, d.w k = 1 ∧
  (∀ i g, X i g = ∑ k, d.w k * toFrac (d.A k) i g) ∧
  (∀ k i, ⌊∑ g, X i g⌋ ≤ ((d.A k i).card : ℤ) ∧ ((d.A k i).card : ℤ) ≤ ⌈∑ g, X i g⌉) ∧
  (∀ k g, ⌊∑ i, X i g⌋ ≤ ((holders (d.A k) g).card : ℤ) ∧
    ((holders (d.A k) g).card : ℤ) ≤ ⌈∑ i, X i g⌉)

/-- Line 5 of Algorithm 1 may use any decomposition that Theorem 1 allows. -/
def IsBvNOracle (D : FracAlloc N G → Decomp N G) : Prop := ∀ X, BvNInput X → IsBvNDecomp X (D X)

/-- "Her favorite available good": on every nonempty set `S`, `pick i S hS` is a good of `S` of
maximal value to `i` (ties broken by any rule). A choice is only asked for on nonempty sets. -/
def IsFavoritePick (I : Instance N G) (pick : PickRule N G) : Prop :=
  ∀ i S (hS : S.Nonempty), pick i S hS ∈ S ∧ ∀ g ∈ S, I.v i g ≤ I.v i (pick i S hS)

/-- One event of the eating protocol. If time is left and some good is not fully consumed, every
agent eats `pick i avail` at rate one until the time budget ends or a good being eaten runs out
(the minimum runs over the goods actually being eaten, so every divisor is at least one). -/
noncomputable def eatStep [Nonempty N] (pick : PickRule N G) (s : EatState N G) :
    EatState N G :=
  let avail := univ.filter fun g => 0 < s.rem g
  if h : 0 < s.τ ∧ avail.Nonempty then
    let e : N → G := fun i => pick i avail h.2
    let k : G → ℕ := fun g => (univ.filter fun i => e i = g).card
    let δ : ℝ := min s.τ ((univ.image e).inf' (univ_nonempty.image e) fun g => s.rem g / k g)
    ⟨fun g => s.rem g - k g * δ, fun i g => s.X i g + if e i = g then δ else 0, s.τ - δ⟩
  else s

/-- `Eating(M', 1)` (p. 9): the partial fractional allocation after one unit of eating time on the
goods `M'`. Each non-final event exhausts a good, so `|G| + 1` events suffice; further iterations
are no-ops. -/
noncomputable def eating [Nonempty N] (pick : PickRule N G) (M' : Finset G) :
    FracAlloc N G :=
  ((eatStep pick)^[Fintype.card G + 1] ⟨fun g => if g ∈ M' then 1 else 0, fun _ _ => 0, 1⟩).X

/-- Algorithm 1 for `T` stages on the goods `M'`, as a lottery over stage histories `[B¹, …, Bᵀ]`:
eat for one unit, decompose by `D`, sample `Aᵏ` with weight `wᵏ`, recurse on `M' \ ⋃ᵢ Aᵏᵢ`. -/
noncomputable def rpsHist [Nonempty N] (pick : PickRule N G) (D : FracAlloc N G → Decomp N G) :
    ℕ → Finset G → List (ℝ × List (IntAlloc N G))
  | 0, _ => [(1, [])]
  | T + 1, M' =>
    let d := D (eating pick M')
    (List.finRange d.q).flatMap fun k =>
      (rpsHist pick D T (M' \ univ.biUnion (d.A k))).map fun e => (d.w k * e.1, d.A k :: e.2)

/-- `B_i = ⋃_t B^t_i`. -/
def unionHist (H : List (IntAlloc N G)) : IntAlloc N G := fun i => (H.map (· i)).foldr (· ∪ ·) ∅

/-- The goods allocated to some agent in some stage of the history `H`. -/
def allocatedGoods (H : List (IntAlloc N G)) : Finset G :=
  univ.filter fun g => ∃ B ∈ H, ∃ i, g ∈ B i

/-- The randomized allocation of `T` stages of Algorithm 1 on `M'`. -/
noncomputable def rps [Nonempty N] (pick : PickRule N G) (D : FracAlloc N G → Decomp N G)
    (T : ℕ) (M' : Finset G) : Lottery N G :=
  (rpsHist pick D T M').map fun e => (e.1, unionHist e.2)

/-- The number of stages `⌈m/n⌉`. -/
noncomputable def stages (N G : Type*) [Fintype N] [Fintype G] : ℕ :=
  ⌈(Fintype.card G : ℝ) / Fintype.card N⌉₊

/-- Algorithm 1 (p. 10): `⌈m/n⌉` stages on all goods. -/
noncomputable def algorithm1 [Nonempty N] (pick : PickRule N G)
    (D : FracAlloc N G → Decomp N G) : Lottery N G :=
  rps pick D (stages N G) univ

end ExAnteExPost.RPS



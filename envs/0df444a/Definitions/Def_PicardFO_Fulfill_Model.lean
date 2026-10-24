-- Prove2me | Definitions.Def_PicardFO_Fulfill_Model
-- name    : PicardFO_Fulfill_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:42.44312+00:00
-- url     : https://prove2.me/theorems/995d25f0-f9a8-49f3-b45e-2c8c64dc93ed
-- title:
--   Fulfillment optimization: dynamics, feasible actions, Assumptions 1–3, Algorithm 1 with partition by products, and the exhausted-node sets Q_t (pp. 4–6)
-- statement:
--   The **fulfillment optimization (FO) problem** (§3) has $I$ products $i \in [I]$ and $J$ nodes $j \in [J]$. A state $s = (x, c)$ records the inventory $x_{i,j} \in \mathbb R$ of product $i$ at node $j$ and the remaining capacity $c_j \in \mathbb R$ of node $j$. An order (disturbance) $\omega$ is for a product $i(\omega)$ and may carry further data (rewards) that the policy reads. An action is either a node $j \in [J]$ or $0 = a_\phi$ (do not fulfil). Action $j$ is feasible for an order of product $i$ iff $c_j > 0$ and $x_{i,j} > 0$; action $0$ is always feasible. Serving the order with action $a$ updates
--   $$
--   c \leftarrow c - e_a, \qquad x \leftarrow x - e_{i(\omega), a},
--   $$
--   and action $0$ changes nothing. This is a controlled dynamical system in the sense of `PicardFO.Fulfill.Picard`.
--
--   A policy $\pi(s, \omega)$ is **feasible** if it always picks a feasible action. The paper's three assumptions on $\pi$ (p. 6) are:
--
--   1. *Inventory Independence:* for an order of product $i$, $\pi((x, c), \omega)$ depends on $x$ only through $(x_{i,j})_{j \in [J]}$.
--   2. *Consistency:* if $\pi((x, c), \omega) \ne j'$ and $(x', c')$ differs from $(x, c)$ only in $x_{i(\omega), j'}$ and $c_{j'}$, then $\pi((x', c'), \omega) \in \{\pi((x, c), \omega), j'\}$.
--   3. *Monotonicity:* if $\pi((x, c), \omega) = j \in [J]$, then adding one unit of inventory of product $i(\omega)$ at node $j$ leaves the decision $j$ unchanged; and adding one unit of capacity at any node with positive capacity leaves the decision unchanged.
--
--   **Algorithm 1 with partition by products** (p. 4): an ownership map assigns each product to a process, and order $t$ is handled by the owner of its product $i(\omega_t)$. The sequential run, the process runs and the cache $\alpha^k$ are those of the general Picard iteration for this system and this assignment.
--
--   For $n \ge 0$, $Q_n$ is the set of nodes with positive initial capacity whose sequential capacity is no longer positive in one of the first $n$ states $s_1, \dots, s_n$:
--   $$
--   Q_n = \{\, j \in [J] : c_{1,j} > 0 \text{ and } c^{\mathrm{seq}}_{t,j} \le 0 \text{ for some } 1 \le t \le n \,\}.
--   $$
--   $|Q_T|$ is the paper's $\mathcal Q_T$, the number of nodes that run out of capacity in the sequential run (corrected reading, see the theorems).
--
--   **Formalization Note** Actions are `Option (Fin J)` with `none` for the paper's action $0 = a_\phi$. Products are `Fin I`, nodes `Fin J`, orders `ω : ℕ → Ω` with product map `prod : Ω → Fin I`, processes an arbitrary type `ι` with ownership map `own : Fin I → ι` (the paper's partition $I_1, \dots, I_M$ of $[I]$ is `own⁻¹{m}`). Orders are 0-based: Lean order `t` is the paper's order $t + 1$, `seqState … t` is the paper's $s_{t+1}$ (the state before Lean order `t`, equivalently the appendix's state after $t$ orders), and `Q … n` is the paper's $Q_n$, so `Q … 0 = ∅`. Assumption 2 is read with $j' \ne \pi((x,c),\omega)$; read literally (allowing $j' = \pi((x,c),\omega) = j$) it would force a policy choosing $j$ to keep choosing $j$ after $c_j$ is set to $0$, which feasibility forbids, so only the policy that never fulfils would qualify. The first clause of Assumption 3 is for decisions $j \in [J]$ ($e_{i,0}$ is undefined); the second for every decision, including $0$. The predicate is named `MonotonePolicy` to avoid a clash with Mathlib's `Monotone`.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, pp. 4–6, §3 (FO problem, partition by products, p. 4), §3.1 (τ_j and Q_t, p. 5), §3.2 (Assumptions 1–3, p. 6)

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Picard

namespace PicardFO.Fulfill

/-- A state of the fulfillment-optimization (FO) problem (§3, p. 4): `x i j` is the inventory of
product `i` at node `j`, `c j` the remaining capacity of node `j`. -/
structure State (I J : ℕ) where
  x : Fin I → Fin J → ℝ
  c : Fin J → ℝ

variable {I J : ℕ}

/-- Feasible fulfillment actions for an order of product `i` (§3, p. 4): `none` (the paper's
action `0 = aϕ`, do not fulfil) is always feasible; `some j` is feasible iff node `j` has
positive capacity and positive inventory of product `i`. -/
def Feasible (s : State I J) (i : Fin I) : Option (Fin J) → Prop
  | none => True
  | some j => 0 < s.c j ∧ 0 < s.x i j

/-- FO dynamics (§3, p. 4): `c ↦ c - e_a`, `x ↦ x - e_{i,a}`; action `none` changes nothing. -/
noncomputable def step (s : State I J) (i : Fin I) : Option (Fin J) → State I J
  | none => s
  | some j => ⟨Function.update s.x i (Function.update (s.x i) j (s.x i j - 1)),
                Function.update s.c j (s.c j - 1)⟩

/-- The FO problem as a dynamical system: an order (disturbance) `w` is for product `prod w`. -/
noncomputable def foSystem (I J : ℕ) (Ω : Type*) (prod : Ω → Fin I) :
    System (State I J) (Option (Fin J)) Ω where
  feasible s w a := Feasible s (prod w) a
  aPhi := none
  aPhi_feasible _ _ := trivial
  f s a w := step s (prod w) a

variable {Ω ι : Type*}

/-- The policy only takes feasible actions: `π(s, ω) ∈ A(s)`. -/
def PolicyFeasible (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J)) : Prop :=
  ∀ s w, Feasible s (prod w) (π s w)

/-- Assumption 1 (Inventory Independence), p. 6: the decision for an order of product
`i = prod w` depends on the inventory only through the inventories of product `i`. -/
def InvIndep (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J)) : Prop :=
  ∀ (x x' : Fin I → Fin J → ℝ) (c : Fin J → ℝ) (w : Ω),
    (∀ j, x (prod w) j = x' (prod w) j) → π ⟨x, c⟩ w = π ⟨x', c⟩ w

/-- Assumption 2 (Consistency), p. 6, read with `j' ≠ π((x, c), ω)`: if `s'` differs from `s`
at most in the inventory `x (prod w) j'` and the capacity `c j'` of one node `j'` that `π` does
not choose at `s`, then `π s' w` is either `π s w` or `j'`. -/
def Consistent (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J)) : Prop :=
  ∀ (s s' : State I J) (w : Ω) (j' : Fin J), π s w ≠ some j' →
    (∀ i j, (i ≠ prod w ∨ j ≠ j') → s'.x i j = s.x i j) →
    (∀ j, j ≠ j' → s'.c j = s.c j) →
    π s' w = π s w ∨ π s' w = some j'

/-- Assumption 3 (Monotonicity), p. 6: (a) adding one unit of inventory of product `prod w` at
the node `j` chosen by `π` leaves the decision `j` unchanged; (b) adding one unit of capacity at
any node `j'` with positive capacity leaves the decision (whatever it is, `none` included)
unchanged. -/
def MonotonePolicy (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J)) : Prop :=
  (∀ (s : State I J) (w : Ω) (j : Fin J), π s w = some j →
      π ⟨Function.update s.x (prod w) (Function.update (s.x (prod w)) j (s.x (prod w) j + 1)),
          s.c⟩ w = some j) ∧
  (∀ (s : State I J) (w : Ω) (j' : Fin J), 0 < s.c j' →
      π ⟨s.x, Function.update s.c j' (s.c j' + 1)⟩ w = π s w)

/-- Sequential FO states: `seqState prod π s₁ ω t` is the state before order `t` (0-based), i.e.
the paper's `s_{t+1} = (x^{seq}_{t+1}, c^{seq}_{t+1})`; `seqState … 0 = s₁`. -/
noncomputable def seqState (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J)) (s₁ : State I J)
    (ω : ℕ → Ω) (t : ℕ) : State I J :=
  (foSystem I J Ω prod).seqState π s₁ ω t

/-- Sequential FO action at order `t` (0-based), the paper's `a^{seq}_{t+1}`. -/
noncomputable def seqAct (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J)) (s₁ : State I J)
    (ω : ℕ → Ω) (t : ℕ) : Option (Fin J) :=
  (foSystem I J Ω prod).seqAct π s₁ ω t

/-- Partition by products (p. 4): order `t` goes to the process `own (prod (ω t))` owning its
product. -/
def orderProc (prod : Ω → Fin I) (ω : ℕ → Ω) (own : Fin I → ι) (t : ℕ) : ι :=
  own (prod (ω t))

/-- Action of process `m` at order `t` in state `s`, with previous cache `α` (Algorithm 1,
lines 6–7, FO problem, partition by products). -/
noncomputable def procAct (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (ω : ℕ → Ω) (own : Fin I → ι) (α : ℕ → Option (Fin J)) (m : ι) (s : State I J) (t : ℕ) :
    Option (Fin J) :=
  (foSystem I J Ω prod).procAct π ω (orderProc prod ω own) α m s t

/-- State of process `m` before order `t` when it simulates with cache `α` (Algorithm 1,
lines 4 and 8). In iteration `k ≥ 1` of the paper process `m` uses `α = cache … (k - 1)`. -/
noncomputable def procState (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (α : ℕ → Option (Fin J)) (m : ι) (t : ℕ) :
    State I J :=
  (foSystem I J Ω prod).procState π s₁ ω (orderProc prod ω own) α m t

/-- The cache `α^k_t` of Algorithm 1 on the FO problem with partition by products:
`cache … 0 = fun _ => none` and `cache … k` is the cache after iteration `k`. -/
noncomputable def cache (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J))
    (s₁ : State I J) (ω : ℕ → Ω) (own : Fin I → ι) (k t : ℕ) : Option (Fin J) :=
  (foSystem I J Ω prod).cache π s₁ ω (orderProc prod ω own) k t

open Classical in
/-- `Q prod π s₁ ω n`: the nodes with positive initial capacity whose sequential capacity is
no longer positive at one of the first `n` states `seqState 0, …, seqState (n - 1)` (the paper's
`s_1, …, s_n`). This is the paper's `Q_n` (§3.1, p. 5; Lemma A.1, p. 12) with "runs out"
read as `c ≤ 0`; `Q … 0 = ∅`. -/
noncomputable def Q (prod : Ω → Fin I) (π : State I J → Ω → Option (Fin J)) (s₁ : State I J)
    (ω : ℕ → Ω) (n : ℕ) : Finset (Fin J) :=
  Finset.univ.filter fun j => 0 < s₁.c j ∧ ∃ u < n, (seqState prod π s₁ ω u).c j ≤ 0

end PicardFO.Fulfill



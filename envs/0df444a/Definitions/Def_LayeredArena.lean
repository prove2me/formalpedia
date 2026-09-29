-- Prove2me | Definitions.Def_LayeredArena
-- name    : LayeredArena
-- status  : Definition
-- author  : @Grace
-- created : 2026-08-04T23:03:25.380552+00:00
-- url     : https://prove2.me/theorems/9bbfd04e-daa8-438c-be20-92e3f7f8cc20
-- title:
--   Layered arena: the hard MDP family of the $\sqrt{DSAn}$ lower bound
-- statement:
--   The combinatorial skeleton of the hard MDP family used in the proof of the $\Omega(\sqrt{DSAn})$ minimax regret lower bound (Lattimore--Szepesvari, *Bandit Algorithms*, Theorem 38.7).
--
--   A **layered arena** on $S$ states and $A$ actions consists of a rooted tree whose leaves all sit at the *same* depth $d$, together with two distinguished absorbing-ish states $s_g$ (`good`, reward $1$) and $s_b$ (`bad`, reward $0$), and a distinguished leaf--action pair $(s_\star, a_\star)$ carrying a planted advantage.  From $s_g$ or $s_b$ the chain stays put with probability $1-\delta$ and restarts at the root with probability $\delta$; at an internal node the chosen action descends deterministically to a child; at a leaf the chosen action reaches $s_g$ with probability $\tfrac12$, raised to $\tfrac12+\Delta$ at the single planted pair.  The resulting object is packaged as a `FiniteMDP` by `toMDP`.
--
--   Uniform leaf depth is a deliberate strengthening of the book, which takes "a tree of minimum depth".  With leaves at two different depths an episode through a shallow leaf is one round shorter, worth $\approx \delta/2$ of gain, whereas the planted advantage is only $\Delta = \Theta(\sqrt{kD/n})$; for large $n$ the optimal gain would then be attained at a *bad* shallow leaf and Claim 38.11 would fail.  With every leaf at depth $d$ each root-to-leaf path has length exactly $d$, so the episode length is $d + 1 + \mathrm{Geom}(\delta)$ under *every* policy — precisely the policy-independence the regret decomposition needs.
--
--   The file also fixes the Bellman certificate data (`best`, `gain`, `bias`, `optPolicy`) and the counting primitives used in the change-of-measure step. `truncCount Ecnt N h s a` records how often the pair $(s,a)$ is played among the first $N$ rounds counted by the $0/1$ indicator `Ecnt`. This replaces the stopping time $\tau$ of the book's Step 2: it yields the identity $\sum_j T_j = \min(\text{total}, N)$ and the bound $T_j \le N_n(s,a)$ *pathwise*, with no measurability side conditions.
-- source:
--   Tor Lattimore and Csaba Szepesvari, Bandit Algorithms, Cambridge University Press 2020, Chapter 38 (Markov Decision Processes), Section 38.7 "Notes"/proof of Theorem 38.7, pp. 496-501; construction of the hard MDP family and Claims 38.9-38.11.

import Definitions.Def_FiniteMDPLearning

open scoped NNReal
open Finset

namespace BanditAlgorithm

/-! # The layered arena of the L&S §38.7 lower-bound construction

A *layered arena* is the combinatorial skeleton of the MDP built in the proof of
L&S Theorem 38.7: a rooted tree whose leaves all sit at the *same* depth `d`,
together with two distinguished states `good` and `bad` carrying reward `1` and
`0`, and a distinguished leaf–action pair `(specialLeaf, specialAction)` at which
the probability of reaching `good` is raised from `1/2` to `1/2 + Δ`.

Uniform depth is a deliberate deviation from the book, which takes "a tree of
minimum depth".  With leaves at two different depths an episode through a shallow
leaf is one round shorter, which is worth `≈ δ/2` of gain, whereas the planted
advantage is only `Δ = Θ(√(kD/n))`; for large `n` the optimal gain would then be
attained at a *bad* shallow leaf and Claim 38.11 would fail.  With all leaves at
depth `d` every root-to-leaf path has length exactly `d`, so the episode length is
`d + 1 + Geom(δ)` under *every* policy — precisely the policy-independence the
regret decomposition of Claim 38.11 needs. -/
structure LayeredArena (S A : ℕ) where
  /-- The common depth of all leaves. -/
  depth : ℕ
  /-- The rewarding state `s_g`. -/
  good : Fin S
  /-- The unrewarding state `s_b`. -/
  bad : Fin S
  /-- The decision state `s∘`, the root of the tree. -/
  root : Fin S
  /-- The leaf carrying the planted advantage. -/
  specialLeaf : Fin S
  /-- The action carrying the planted advantage. -/
  specialAction : Fin A
  /-- A fallback action, used where the choice is irrelevant. -/
  defaultAction : Fin A
  /-- The level of a tree node; junk on `good` and `bad`. -/
  lvl : Fin S → ℕ
  /-- The child of a tree node reached by an action. -/
  child : Fin S → Fin A → Fin S
  /-- Marks the root-to-`specialLeaf` path. -/
  onPath : Fin S → Bool
  /-- The action continuing the path at an internal node. -/
  pathAction : Fin S → Fin A
  good_ne_bad : good ≠ bad
  root_ne_good : root ≠ good
  root_ne_bad : root ≠ bad
  lvl_root : lvl root = 0
  lvl_le : ∀ s, s ≠ good → s ≠ bad → lvl s ≤ depth
  /-- Children of an internal node are tree nodes one level deeper. -/
  lvl_child : ∀ s a, s ≠ good → s ≠ bad → lvl s < depth →
    lvl (child s a) = lvl s + 1
  child_ne_good : ∀ s a, s ≠ good → s ≠ bad → lvl s < depth → child s a ≠ good
  child_ne_bad : ∀ s a, s ≠ good → s ≠ bad → lvl s < depth → child s a ≠ bad
  onPath_root : onPath root = true
  /-- The path is closed under taking parents: a child can only be on the path
  if its parent is.  (The converse implication with a *fixed* action is
  `onPath_child_mpr`; the two are deliberately *not* packaged as an `iff`,
  because when a level is narrower than the branching factor two actions lead to
  the same child and an `iff` would be unsatisfiable.) -/
  onPath_child_mp : ∀ s a, s ≠ good → s ≠ bad → lvl s < depth →
    onPath (child s a) = true → onPath s = true
  /-- The path descends through `pathAction`. -/
  onPath_child_mpr : ∀ s, s ≠ good → s ≠ bad → lvl s < depth →
    onPath s = true → onPath (child s (pathAction s)) = true
  /-- The only leaf on the path is the special one. -/
  onPath_leaf : ∀ s, s ≠ good → s ≠ bad → lvl s = depth → onPath s = true →
    s = specialLeaf
  specialLeaf_ne_good : specialLeaf ≠ good
  specialLeaf_ne_bad : specialLeaf ≠ bad
  /-- The planted pair is a *leaf*–action pair.  Without this the advantage
  could be planted at an internal node, where `goodProb` never enters the
  transition kernel, and the regret decomposition of Claim 38.11 would charge a
  gap that the MDP does not pay. -/
  specialLeaf_lvl : lvl specialLeaf = depth
  onPath_specialLeaf : onPath specialLeaf = true

namespace LayeredArena

variable {S A : ℕ}

/-- The two-point probability vector `p·δ_x + q·δ_y`. -/
def twoPoint (x y : Fin S) (p q : ℝ≥0) : Fin S → ℝ≥0 :=
  fun s' ↦ (if s' = x then p else 0) + (if s' = y then q else 0)

lemma sum_twoPoint [NeZero S] (x y : Fin S) (p q : ℝ≥0) :
    ∑ s', twoPoint x y p q s' = p + q := by
  classical
  simp [twoPoint, Finset.sum_add_distrib]

lemma sum_twoPoint_mul [NeZero S] (x y : Fin S) (p q : ℝ≥0) (v : Fin S → ℝ) :
    ∑ s', ((twoPoint x y p q s' : ℝ≥0) : ℝ) * v s' = p * v x + q * v y := by
  classical
  simp [twoPoint, add_mul, Finset.sum_add_distrib,
    apply_ite (fun r : ℝ≥0 ↦ (r : ℝ)), ite_mul]

variable (E : LayeredArena S A)

/-- The probability of reaching `good` from a leaf: `1/2`, raised to `1/2 + Δ`
at the single planted leaf–action pair. -/
noncomputable def goodProb (Δ : ℝ≥0) (s : Fin S) (a : Fin A) : ℝ≥0 :=
  1 / 2 + (if s = E.specialLeaf ∧ a = E.specialAction then Δ else 0)

lemma goodProb_le_one {Δ : ℝ≥0} (hΔ : Δ ≤ 1 / 2) (s : Fin S) (a : Fin A) :
    E.goodProb Δ s a ≤ 1 := by
  unfold goodProb
  split_ifs with h
  · calc (1 : ℝ≥0) / 2 + Δ ≤ 1 / 2 + 1 / 2 := by gcongr
      _ = 1 := by norm_num
  · simp only [add_zero]
    norm_num

/-- The transition rows.  From `good` (resp. `bad`) the chain stays put with
probability `1 - δ` and returns to the root with probability `δ`; from an internal
node the chosen action moves deterministically to the corresponding child; from a
leaf the chosen action reaches `good` with probability `goodProb`. -/
noncomputable def rows (δ Δ : ℝ≥0) (s : Fin S) (a : Fin A) : Fin S → ℝ≥0 :=
  if s = E.good then twoPoint E.good E.root (1 - δ) δ
  else if s = E.bad then twoPoint E.bad E.root (1 - δ) δ
  else if E.lvl s < E.depth then twoPoint (E.child s a) (E.child s a) 1 0
  else twoPoint E.good E.bad (E.goodProb Δ s a) (1 - E.goodProb Δ s a)

lemma sum_rows [NeZero S] {δ Δ : ℝ≥0} (hδ : δ ≤ 1) (hΔ : Δ ≤ 1 / 2)
    (s : Fin S) (a : Fin A) : ∑ s', E.rows δ Δ s a s' = 1 := by
  classical
  unfold rows
  split_ifs
  · rw [sum_twoPoint, tsub_add_cancel_of_le hδ]
  · rw [sum_twoPoint, tsub_add_cancel_of_le hδ]
  · rw [sum_twoPoint, add_zero]
  · rw [sum_twoPoint, add_tsub_cancel_of_le (E.goodProb_le_one hΔ s a)]

@[simp] lemma rows_good {δ Δ : ℝ≥0} (a : Fin A) :
    E.rows δ Δ E.good a = twoPoint E.good E.root (1 - δ) δ := by
  unfold rows; rw [if_pos rfl]

@[simp] lemma rows_bad {δ Δ : ℝ≥0} (a : Fin A) :
    E.rows δ Δ E.bad a = twoPoint E.bad E.root (1 - δ) δ := by
  unfold rows; rw [if_neg E.good_ne_bad.symm, if_pos rfl]

lemma rows_internal {δ Δ : ℝ≥0} {s : Fin S} (a : Fin A) (hg : s ≠ E.good)
    (hb : s ≠ E.bad) (hint : E.lvl s < E.depth) :
    E.rows δ Δ s a = twoPoint (E.child s a) (E.child s a) 1 0 := by
  unfold rows; rw [if_neg hg, if_neg hb, if_pos hint]

lemma rows_leaf {δ Δ : ℝ≥0} {s : Fin S} (a : Fin A) (hg : s ≠ E.good)
    (hb : s ≠ E.bad) (hint : ¬ E.lvl s < E.depth) :
    E.rows δ Δ s a
      = twoPoint E.good E.bad (E.goodProb Δ s a) (1 - E.goodProb Δ s a) := by
  unfold rows; rw [if_neg hg, if_neg hb, if_neg hint]

/-- The MDP of the L&S §38.7 lower-bound construction: reward `1` exactly on
`good`, transitions given by `rows`. -/
noncomputable def toMDP [NeZero S] {δ Δ : ℝ≥0} (hδ : δ ≤ 1) (hΔ : Δ ≤ 1 / 2) :
    FiniteMDP S A where
  P := E.rows δ Δ
  P_sum_one := E.sum_rows hδ hΔ
  r := fun s _ ↦ if s = E.good then 1 else 0
  r_mem_Icc := by intro s a; split_ifs <;> norm_num

/-- The `0/1` indicator of the leaves — the states whose visits are counted in
the change-of-measure step. -/
def leafNat (s : Fin S) : ℕ :=
  if s ≠ E.good ∧ s ≠ E.bad ∧ E.lvl s = E.depth then 1 else 0

/-- The per-round growth factor `x = 1 + δ/2` of the supermartingale. -/
noncomputable def mx (δ : ℝ) : ℝ := 1 + δ / 2

/-- The mean length of one episode: a descent of `depth` steps, one gamble, and
a `Geom(δ)` sojourn of mean `1/δ`. -/
noncomputable def epiLen (δ : ℝ) : ℝ := 1 / δ + (E.depth : ℝ) + 1

/-- The best `good`-probability available in the subtree below a node: `1/2 + Δ`
on the planted path, `1/2` off it. -/
noncomputable def best (Δ : ℝ) (s : Fin S) : ℝ :=
  1 / 2 + (if E.onPath s = true then Δ else 0)

/-- The optimal gain of the construction: `(1/2 + Δ) / (1 + δ(d+1))`.  An episode
costs `d` steps of descent, one gamble, and a `Geom(δ)` sojourn of mean `1/δ`, and
returns `1/2 + Δ` per unit of sojourn. -/
noncomputable def gain (δ Δ : ℝ) : ℝ := (1 / 2 + Δ) / (1 + δ * (E.depth + 1))

/-- The bias of the Bellman certificate.  On the tree it is the value obtained by
backward induction: the best reachable `good`-probability, discounted by `ρ` for
each remaining step of the descent.  Giving every leaf the same bias would be
wrong — the Bellman equation would then fail at the leaves off the planted
path. -/
noncomputable def bias (δ Δ : ℝ) : Fin S → ℝ :=
  fun s ↦
    if s = E.good then 1 / δ
    else if s = E.bad then 0
    else E.best Δ s / δ - E.gain δ Δ * ((E.depth : ℝ) - E.lvl s + 1)

/-- The deterministic memoryless policy of the certificate: descend along the
planted path, and gamble with the planted action at the special leaf. -/
noncomputable def optPolicy : Fin S → Fin A :=
  fun s ↦
    if s = E.good ∨ s = E.bad then E.defaultAction
    else if E.lvl s < E.depth then E.pathAction s
    else if s = E.specialLeaf then E.specialAction
    else E.defaultAction

end LayeredArena

variable {S A : ℕ}

/-- The running count of `Ecnt` over the rounds strictly before `t`. -/
def prefixCount {n : ℕ} (Ecnt : Fin S → ℕ) (h : MDPTrajectory S A n) (t : ℕ) : ℕ :=
  ∑ u : Fin n, if (u : ℕ) < t then Ecnt (h u).1 else 0

/-- `T_j`: the number of rounds at which the pair `(s, a)` is played among the
first `N` rounds counted by `Ecnt`. -/
def truncCount {n : ℕ} (Ecnt : Fin S → ℕ) (N : ℕ) (h : MDPTrajectory S A n)
    (s : Fin S) (a : Fin A) : ℕ :=
  ∑ t : Fin n, if h t = (s, a) ∧ prefixCount Ecnt h (t : ℕ) < N then 1 else 0

/-- The pairs at which the count accrues. -/
def countedPairs (Ecnt : Fin S → ℕ) : Finset (Fin S × Fin A) :=
  Finset.univ.filter fun p : Fin S × Fin A ↦ Ecnt p.1 = 1

lemma mem_countedPairs {Ecnt : Fin S → ℕ} {p : Fin S × Fin A} :
    p ∈ countedPairs Ecnt ↔ Ecnt p.1 = 1 := by
  simp [countedPairs]

end BanditAlgorithm



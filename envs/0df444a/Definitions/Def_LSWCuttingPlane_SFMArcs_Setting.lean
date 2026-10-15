-- Prove2me | Definitions.Def_LSWCuttingPlane_SFMArcs_Setting
-- name    : LSWCuttingPlane_SFMArcs_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:03.072328+00:00
-- url     : https://prove2.me/theorems/23483a8d-d421-46fb-9c88-d97616661f82
-- title:
--   §13.1, §13.3, §15.2, pp. 74, 76–77, 82, 84–85 — submodularity, B(f), BFS of a permutation, ring family of a digraph, R(i), Q(i), consistency, upper, lower
-- statement:
--   Let $V = [n] = \{1, \dots, n\}$ be a ground set and $f : 2^V \to \mathbb Z$ a set function. For $S \subseteq V$ and $i \in V$ write $S + i = S \cup \{i\}$ and $S - i = S \setminus \{i\}$.
--
--   1. **Submodularity** (Definition 58). $f$ is submodular if
--   $$f(T + i) - f(T) \le f(S + i) - f(S) \qquad \text{for all } S \subseteq T \text{ and } i \in V \setminus T.$$
--   2. **Base polyhedron.** For $y \in \mathbb R^n$ and $S \subseteq V$ write $y(S) = \sum_{i \in S} y_i$. The base polyhedron of $f$ is
--   $$\mathcal B(f) = \{ y \in \mathbb R^n : y(S) \le f(S) \ \forall S \subseteq V,\ y(V) = f(V) \}.$$
--   3. **BFS of a permutation** (Theorem 62). For a permutation $v_1, \dots, v_n$ of $V$, the BFS with this defining permutation is the vector $h$ with $h_{v_i} = f(\{v_1, \dots, v_i\}) - f(\{v_1, \dots, v_{i-1}\})$. We say $v_i$ precedes $v_j$ when $i < j$.
--   4. **Ring family of a digraph.** A set $A$ of arcs on $V$ represents the ring family $\mathcal F_A = \{ S \subseteq V : (i, j) \in A,\ i \in S \Rightarrow j \in S \}$. The digraph is assumed acyclic. $R(i)$ is the set of descendants of $i$ and $Q(i)$ the set of ancestors of $i$, both including $i$ itself.
--   5. **Consistency** (Definition 74). A permutation, or the BFS it defines, is consistent with the arc $(i, j)$ if $j$ precedes $i$, and consistent with $A$ if it is consistent with every arc of $A$.
--   6. **upper and lower** (p. 84). $\mathrm{upper}(i) = f(R(i)) - f(R(i) - i)$ and $\mathrm{lower}(i) = f(V \setminus Q(i) + i) - f(V \setminus Q(i))$.
--   7. **Non-degeneracy** (p. 77). A vector $y$ is non-degenerate if it has both a strictly positive and a strictly negative entry.
--   8. A **minimizer of $f$ over the ring family** of $A$ is a set $S \in \mathcal F_A$ with $f(S) \le f(T)$ for every $T \in \mathcal F_A$.
--   9. A **convex combination of consistent BFS's** is $y = \sum_k \lambda^{(k)} y^{(k)}$ over a finite index set, with $\lambda^{(k)} \ge 0$, $\sum_k \lambda^{(k)} = 1$, and each $y^{(k)}$ the BFS of a permutation consistent with $A$.
--   10. **Moving a set to the front** (proof of Lemma 79). The permutation $\tau$ is obtained from $\sigma$ by moving $T$ to the front if, under $\tau$, every element of $T$ precedes every element of $V \setminus T$, and the relative order of two elements both in $T$ or both outside $T$ is the one of $\sigma$.
--
--   These are the objects of the paper's strongly polynomial algorithms for submodular function minimization over a ring family; Lemmas 76–80 are stated in terms of them.
--
--   **Formalization Note** The ground set is `Fin n` (0-based indices instead of the paper's $1, \dots, n$); sets are `Finset (Fin n)`, $f$ is integer valued (the standing assumption of §13.1) and vectors are real. A permutation `σ : Equiv.Perm (Fin n)` is read as a position map: `u` precedes `v` iff `σ u < σ v`. The BFS of a permutation is *defined* by the formula of Theorem 62; the theorem itself (these vectors are exactly the vertices of $\mathcal B(f)$) is not formalized, because the lemmas of the mission use BFS's only through their defining permutations. Arcs are a relation `A : Fin n → Fin n → Prop`; $R$ and $Q$ use the reflexive–transitive closure. The page prints the constraint of $\mathcal B(f)$ as "$\forall S \not\subseteq V$", a slip for $S \subseteq V$; the definition quantifies over all $S \subseteq V$ (for $S = V$ the inequality is implied by the equality). `ymax`/`ymin` are $\max_j y_j$, $\min_j y_j$ and need `n ≠ 0`.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, pp. 74, 76–77, 82, 84–85, §13.1 Definition 58, §13.3 Theorem 62, §15.2.1 Definition 74, §15.2.2

import Mathlib

namespace LSWCuttingPlane.SFMArcs

open Finset

/-- §13.1, p. 74, Definition 58 (Submodularity): `f : 2^V → ℤ` is submodular if
`f(T + i) − f(T) ≤ f(S + i) − f(S)` for any `S ⊆ T` and `i ∈ V \ T`.
The ground set `V = [n]` is `Fin n` (0-based). -/
def Submodular {n : ℕ} (f : Finset (Fin n) → ℤ) : Prop :=
  ∀ (S T : Finset (Fin n)) (i : Fin n), S ⊆ T → i ∉ T →
    f (insert i T) - f T ≤ f (insert i S) - f S

/-- §13.3, p. 76: the shorthand `y(S) = ∑_{i ∈ S} y_i`. -/
def ysum {n : ℕ} (y : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, y i

/-- §13.3, p. 76: the base polyhedron
`B(f) = {y ∈ ℝ^n : y(S) ≤ f(S) ∀ S ⊆ V, y(V) = f(V)}`
(the page prints `∀ S ⊈ V`, a slip for `S ⊆ V`). -/
def baseB {n : ℕ} (f : Finset (Fin n) → ℤ) : Set (Fin n → ℝ) :=
  {y | (∀ S : Finset (Fin n), ysum y S ≤ (f S : ℝ)) ∧ ysum y Finset.univ = (f Finset.univ : ℝ)}

/-- A permutation of the ground set is read as a position map: `u` precedes `v` iff `σ u < σ v`.
`before σ v` is the set of elements preceding `v`, i.e. `{v_1, …, v_{i-1}}` when `v = v_i`. -/
def before {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => σ u < σ v)

/-- §13.3, p. 76, Theorem 62: the BFS of `B(f)` with defining permutation `σ`,
`h_{v_i} = f({v_1, …, v_i}) − f({v_1, …, v_{i−1}})`. -/
def bfs {n : ℕ} (f : Finset (Fin n) → ℤ) (σ : Equiv.Perm (Fin n)) (v : Fin n) : ℝ :=
  ((f (insert v (before σ v)) - f (before σ v) : ℤ) : ℝ)

/-- §15.2.1, p. 82: the ring family represented by the digraph `D = (V, A)`:
`S ∈ F` iff for every arc `(i, j) ∈ A`, `i ∈ S` implies `j ∈ S`. -/
def ringFamily {n : ℕ} (A : Fin n → Fin n → Prop) : Set (Finset (Fin n)) :=
  {S | ∀ i j, A i j → i ∈ S → j ∈ S}

/-- §15.2.1, p. 82: the standing assumption that the digraph `A` is acyclic. -/
def Acyclic {n : ℕ} (A : Fin n → Fin n → Prop) : Prop :=
  ∀ i, ¬ Relation.TransGen A i i

open Classical in
/-- §15.2.1, p. 82: `R(i)`, the set of descendants of `i` (including `i` itself). -/
noncomputable def R {n : ℕ} (A : Fin n → Fin n → Prop) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Relation.ReflTransGen A i j)

open Classical in
/-- §15.2.1, p. 82: `Q(i)`, the set of ancestors of `i` (including `i` itself). -/
noncomputable def Q {n : ℕ} (A : Fin n → Fin n → Prop) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Relation.ReflTransGen A j i)

/-- §15.2.1, p. 82, Definition 74: a permutation is consistent with `A` if for every arc
`(i, j) ∈ A`, `j` precedes `i`. -/
def Consistent {n : ℕ} (A : Fin n → Fin n → Prop) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j, A i j → σ j < σ i

/-- §15.2.2, p. 84: `upper(i) = f(R(i)) − f(R(i) − i)`. -/
noncomputable def upper {n : ℕ} (f : Finset (Fin n) → ℤ) (A : Fin n → Fin n → Prop)
    (i : Fin n) : ℤ :=
  f (R A i) - f ((R A i).erase i)

/-- §15.2.2, p. 84: `lower(i) = f(V \ Q(i) + i) − f(V \ Q(i))`. -/
noncomputable def lower {n : ℕ} (f : Finset (Fin n) → ℤ) (A : Fin n → Fin n → Prop)
    (i : Fin n) : ℤ :=
  f (insert i (Finset.univ \ Q A i)) - f (Finset.univ \ Q A i)

/-- §13.3, p. 77: `y` is non-degenerate if it has both positive and negative entries. -/
def NonDegenerate {n : ℕ} (y : Fin n → ℝ) : Prop :=
  (∃ i, 0 < y i) ∧ (∃ j, y j < 0)

/-- `max_j y_j`. -/
def ymax {n : ℕ} [NeZero n] (y : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty y

/-- `min_j y_j`. -/
def ymin {n : ℕ} [NeZero n] (y : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty y

/-- A minimizer of `f` over the ring family of `A`. -/
def IsMinimizer {n : ℕ} (A : Fin n → Fin n → Prop) (f : Finset (Fin n) → ℤ)
    (S : Finset (Fin n)) : Prop :=
  S ∈ ringFamily A ∧ ∀ T ∈ ringFamily A, f S ≤ f T

/-- The weights `λ^{(k)}` and defining permutations `σ_k` describe a convex combination of BFS's
of `B(f)`, each consistent with every arc of `A`. -/
def IsConsistentComb {n : ℕ} {ι : Type} [Fintype ι] (A : Fin n → Fin n → Prop)
    (lam : ι → ℝ) (σs : ι → Equiv.Perm (Fin n)) : Prop :=
  (∀ k, 0 ≤ lam k) ∧ (∑ k, lam k = 1) ∧ ∀ k, Consistent A (σs k)

/-- The convex combination `y = ∑_k λ^{(k)} y^{(k)}` of the BFS's `y^{(k)}` with defining
permutations `σ_k`. -/
def combo {n : ℕ} {ι : Type} [Fintype ι] (f : Finset (Fin n) → ℤ) (lam : ι → ℝ)
    (σs : ι → Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun j => ∑ k, lam k * bfs f (σs k) j

/-- Proof of Lemma 79, p. 85: `τ` is obtained from `σ` by moving the set `T` to the front while
preserving the relative order inside `T` and inside `V \ T`. -/
def IsFrontload {n : ℕ} (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n))
    (τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ u v, τ u < τ v ↔ ((u ∈ T ∧ v ∉ T) ∨ ((u ∈ T ↔ v ∈ T) ∧ σ u < σ v))

end LSWCuttingPlane.SFMArcs



-- Prove2me | Definitions.Def_TalagrandConc_Assignment_Basic
-- name    : TalagrandConc_Assignment_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:44.732992+00:00
-- url     : https://prove2.me/theorems/2b71c0a3-6d2a-4e01-82a3-0bed3375b5e7
-- title:
--   Assignments, the optimal cost L_N, α-expanding digraphs and D_u (Chapter 10)
-- statement:
--   Let $N \ge 0$ and let $I = J = \{0, \dots, N-1\}$ be two copies of a set of cardinal $N$. This module fixes the objects of Chapter 10 of Talagrand's article.
--
--   1. **Assignments and their cost.** An assignment is a one-to-one map $\tau$ from $I$ onto $J$, i.e. a permutation of $\{0,\dots,N-1\}$. For a cost matrix $a = (a_{i,j})_{i \in I, j \in J}$ the cost of $\tau$ is $\sum_{i \in I} a_{i,\tau(i)}$, and the optimal cost is
--   $$L_N(a) = \min\Big\{ \sum_{i \in I} a_{i,\tau(i)} \;;\; \tau \text{ assignment} \Big\},$$
--   a minimum over the finitely many permutations. An assignment is **optimal** for $a$ when its cost equals $L_N(a)$.
--   2. **Digraphs and expansion.** A digraph is a subset $D \subseteq I \times J$; for $S \subseteq I$ put $D(S) = \{ j \in J ;\ \exists i \in S,\ (i,j) \in D \}$. For a real $\alpha \ge 2$, $D$ is **$\alpha$-expanding** if for every $S \subseteq I$
--   $$\operatorname{card} S \le \tfrac N2 \Rightarrow \operatorname{card} D(S) \ge \min\big(\alpha \operatorname{card} S, \tfrac N2\big), \qquad \operatorname{card} S \ge \tfrac N2 \Rightarrow \operatorname{card} D(S) \ge N - \tfrac1\alpha (N - \operatorname{card} S).$$
--   The requirement $\alpha \ge 2$ is part of the definition.
--   3. **The threshold digraph.** For $u > 0$ and a cost matrix $X$, $D_u = \{ (i,j) ;\ X_{i,j} \le 2u N^{-1} \log N \}$.
--   4. **The random costs.** The law of the cost matrix whose $N^2$ entries $X_{i,j}$ are independent and uniformly distributed on $[0,1]$: the product over $I \times J$ of Lebesgue measure restricted to $[0,1]$.
--   5. **Median.** $M$ is a median of a real random variable $Z$ when $P(Z \le M) \ge 1/2$ and $P(Z \ge M) \ge 1/2$.
--
--   These are the objects in which the chapter's concentration bound for the random assignment problem is stated.
--
--   **Formalization Note** Cardinalities of subsets of the finite set $I$ or $J$ are `Set.ncard`, exact on finite sets. $L_N$ is `Finset.inf'` over the nonempty finite set of permutations, so it has no junk value. $N^{-1}\log N$ is computed in $\mathbb R$ (it is $0$ at $N = 0, 1$).
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 166, Section 10, Eqs. (10.1)–(10.2); p. 167, definition of D_u

import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.Assignment

open MeasureTheory

/-- Talagrand (1995), p. 166: for a digraph `D ⊆ I × J` and `S ⊆ I`,
`D(S) = { j ∈ J ; ∃ i ∈ S, (i, j) ∈ D }`. Here `I = J = Fin N`. -/
def nbhd {N : ℕ} (D : Set (Fin N × Fin N)) (S : Set (Fin N)) : Set (Fin N) :=
  {j | ∃ i ∈ S, (i, j) ∈ D}

/-- Talagrand (1995), p. 166, Eqs. (10.1)–(10.2): a digraph `D ⊆ I × J` (`I = J = Fin N`) is
`α`-expanding (`α ≥ 2`) if for all subsets `S` of `I`,
`card S ≤ N/2 ⇒ card D(S) ≥ min(α card S, N/2)` and
`card S ≥ N/2 ⇒ card D(S) ≥ N − (1/α)(N − card S)`.
The requirement `α ≥ 2` is part of the definition. Cardinalities of subsets of the finite
type `Fin N` are computed with `Set.ncard` (no junk value: every such set is finite). -/
def IsExpanding (N : ℕ) (α : ℝ) (D : Set (Fin N × Fin N)) : Prop :=
  2 ≤ α ∧ ∀ S : Set (Fin N),
    ((S.ncard : ℝ) ≤ (N : ℝ) / 2 →
        min (α * S.ncard) ((N : ℝ) / 2) ≤ ((nbhd D S).ncard : ℝ)) ∧
    ((N : ℝ) / 2 ≤ S.ncard →
        (N : ℝ) - (1 / α) * ((N : ℝ) - S.ncard) ≤ ((nbhd D S).ncard : ℝ))

/-- Talagrand (1995), p. 166: the cost `∑_{i ∈ I} a_{i, τ(i)}` of the assignment `τ`
(a one-to-one map from `I` onto `J`, here a permutation of `Fin N`) for the cost matrix
`a : I × J → ℝ`. -/
def assignmentCost {N : ℕ} (a : Fin N × Fin N → ℝ) (τ : Equiv.Perm (Fin N)) : ℝ :=
  ∑ i, a (i, τ i)

/-- Talagrand (1995), p. 166: the optimal assignment cost
`L_N = inf { ∑_{i ∈ I} a_{i, τ(i)} ; τ assignment }`, a minimum over the finite nonempty set
of permutations of `Fin N`. -/
def optCost {N : ℕ} (a : Fin N × Fin N → ℝ) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin N))).inf' Finset.univ_nonempty
    (fun τ => assignmentCost a τ)

/-- An optimal assignment for the cost matrix `a`: a permutation `τ` of minimal cost
(Talagrand (1995), p. 167, Corollary 10.2, "an optimal assignment τ"). -/
def IsOptimalAssignment {N : ℕ} (a : Fin N × Fin N → ℝ) (τ : Equiv.Perm (Fin N)) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), assignmentCost a τ ≤ assignmentCost a σ

/-- Talagrand (1995), p. 167: for `u > 0` the digraph
`D_u = { (i, j) ; X_{i,j} ≤ 2 u N⁻¹ log N }` of the cost matrix `X`. -/
noncomputable def digraphU (N : ℕ) (u : ℝ) (X : Fin N × Fin N → ℝ) : Set (Fin N × Fin N) :=
  {p | X p ≤ 2 * u * (N : ℝ)⁻¹ * Real.log N}

/-- Talagrand (1995), p. 166: the law of the cost matrix `(X_{i,j})_{i ∈ I, j ∈ J}` whose
`N²` entries are independent and uniformly distributed over `[0, 1]`: the product over
`Fin N × Fin N` of Lebesgue measure restricted to `[0, 1]`. A point of the sample space is
a cost matrix; its coordinates are the random variables `X_{i,j}`. -/
noncomputable def costLaw (N : ℕ) : Measure (Fin N × Fin N → ℝ) :=
  Measure.pi (fun _ : Fin N × Fin N => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))

end TalagrandConc.Assignment



-- Prove2me | Definitions.Def_HighDimStat_GraphicalModels_Core
-- name    : HighDimStat_GraphicalModels_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:20:10.398933+00:00
-- url     : https://prove2.me/theorems/adb7791b-0a71-47ce-a371-969c79651c1c
-- title:
--   Graph factorization, Markov property and vertex cutsets
-- statement:
--   This file collects Chapter 11's core vocabulary for undirected graphical models on a
--   finite vertex set $V$ with random vector $X : \Omega \to V \to \mathbb R$.
--
--   - **`Factorizes G p`**: the random vector with density $p$ (up to a positive normalizing
--     constant, matching the book's $\propto$) factorizes according to the graph $G$
--     (Definition 11.1, Eq. (11.1)): $p$ is a product, over a family of cliques of $G$, of
--     nonnegative clique-compatibility functions $\psi_C$, each depending only on the
--     coordinates in $C$.
--   - **`IsSeparatingSet G S A B`**: $S$ is a vertex cutset separating $A$ from $B$ — the setup
--     behind Definition 11.5 (p. 350): $S,A,B$ partition $V$, $A,B$ are nonempty, and no edge
--     joins $A$ to $B$.
--   - **`IsMarkov G X hX P`**: $X$ is Markov with respect to $G$ (Definition 11.5): for every
--     vertex cutset $S$ separating $A$ from $B$, $X_A \perp\!\!\!\perp X_B \mid X_S$.
--
--   **Formalization Note** Conditional independence uses Mathlib's `CondIndepFun` notation
--   (`⟂ᵢ[Z, hZ; μ]`), which requires `[StandardBorelSpace Ω]`. `IsSeparatingSet` states the
--   separation property directly (no edges between $A$ and $B$ after removing $S$, with
--   $S,A,B$ partitioning $V$) rather than building general graph-connectivity/components
--   machinery, since this is exactly the property Definition 11.5 uses.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, pp. 347-351 (PDF pp. 367-371), Definitions 11.1, 11.5, Eq. (11.1), (11.4), (11.5)

import Mathlib

namespace HighDimStat.GraphicalModels

open MeasureTheory ProbabilityTheory

/-- Restriction of a full vector `x : V → ℝ` to the coordinates in `A`. -/
def restrictFun {V : Type*} (A : Set V) (x : V → ℝ) : A → ℝ := fun j => x j.1

/-- The random vector `X` factorizes according to the undirected graph `G` (Definition 11.1,
p. 348, Eq. (11.1)): its density `p` (up to a positive normalizing constant `c`, matching the
book's `∝`) is a product, over a family of cliques of `G`, of nonnegative clique-compatibility
functions `ψ C`, each depending only on the coordinates in `C`. -/
def Factorizes {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (p : (V → ℝ) → ℝ) : Prop :=
  ∃ (cliques : Finset (Finset V)) (ψ : Finset V → (V → ℝ) → ℝ) (c : ℝ), 0 < c ∧
    (∀ C ∈ cliques, G.IsClique (↑C : Set V)) ∧
    (∀ C ∈ cliques, ∀ x, 0 ≤ ψ C x) ∧
    (∀ C ∈ cliques, ∀ x y : V → ℝ, (∀ j ∈ C, x j = y j) → ψ C x = ψ C y) ∧
    ∀ x, p x = c * ∏ C ∈ cliques, ψ C x

/-- `S` separates `A` from `B` in `G` — a vertex cutset (the setup behind Definition 11.5,
p. 350): `S, A, B` partition the vertex set, `A` and `B` are both nonempty, and no edge of `G`
joins `A` to `B`. -/
def IsSeparatingSet {V : Type*} (G : SimpleGraph V) (S A B : Set V) : Prop :=
  Disjoint A B ∧ Disjoint A S ∧ Disjoint B S ∧ A ∪ B ∪ S = Set.univ ∧
    A.Nonempty ∧ B.Nonempty ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

/-- `X` is Markov with respect to `G` (Definition 11.5, p. 350): for every vertex cutset `S`
separating `A` from `B`, the sub-vectors `X_A` and `X_B` are conditionally independent given
`X_S`. -/
def IsMarkov {V Ω : Type*} [Fintype V] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (G : SimpleGraph V) (X : Ω → V → ℝ) (hX : Measurable X) (P : Measure Ω)
    [IsProbabilityMeasure P] : Prop :=
  ∀ S A B : Set V, IsSeparatingSet G S A B →
    (fun ω => restrictFun A (X ω)) ⟂ᵢ[fun ω => restrictFun S (X ω),
        measurable_pi_lambda _ (fun j : S => (measurable_pi_apply j.1).comp hX); P]
      (fun ω => restrictFun B (X ω))

end HighDimStat.GraphicalModels



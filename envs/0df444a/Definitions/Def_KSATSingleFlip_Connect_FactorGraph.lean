-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_FactorGraph
-- name    : KSATSingleFlip_Connect_FactorGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:06:35.277181+00:00
-- url     : https://prove2.me/theorems/3ccafa59-4e17-4cfe-a4c6-1b99585a0986
-- title:
--   Factor graphs, locally tree-structured variables, regularity $\mathsf{Reg}$ and complete forcing trees
-- statement:
--   * Factor graph $G(\Phi)$ (Definition 2.1): the bipartite graph on variables and clause positions joining each clause to its scope (`factorGraph`). The ball $B_r(\Phi,v)$ is the radius-$2r$ ball about $v$; `ballVars`, `ballIdx`, and `ballF Φ v r` = its clauses as a formula on the same variable type (variables outside the ball carry no clause of it). `BallIsTree`: the ball's factor graph is acyclic. `degree Φ u`: number of clause positions containing $u$.
--   * $(r,D)$-locally tree-structured (Lemma 2.7): $B_r(\Phi,v)$ is a tree and every variable in it has degree $\le D$ in $\Phi$ (`LocallyTree`).
--   * $\rho = k^{-100\lceil(\ln k)^6\rceil}$ (`rho`), $\eta = (\ln k)^{10}/(64k)$ (`etaC`) (p. 53).
--   * Definition 7.2 with degree cutoff $D$ (the paper's $D_k$): $\mathsf{LT}(\Phi)$: at least $(1-\eta)n$ variables are $(2k+4,D)$-locally tree-structured; $\mathsf{LS}(\Phi)$: $|\{C\in\Phi : \mathrm{vbl}(C)\subseteq A\}| < 2|A|/k$ for all $0<|A|\le\rho n$ (clauses counted by position); $\mathsf{Reg} = \mathsf{LT}\wedge\mathsf{LS}$.
--   * Definition 3.1: $C$ forces $v$ under $\sigma$ if $\mathrm{sat}_\sigma(C) = \{v\}$ (`Forces`). A forcing tree in $\Psi$ under $\sigma$ (`ForcingTree`): a root, a variable set, a set of clause positions, for each clause a parent (which it forces) and a unique child in its scope, every non-root variable the child of exactly one tree clause, and a depth function increasing by one from parent to child (so the structure is a rooted subtree of the factor graph). `CompleteIn T I`: the tree's clauses lie in the sub-formula $\Psi_I$ and every clause of $\Psi_I$ forcing a tree variable is a child clause of it. `size` = number of variables. `HasSmallCFT Ψ I σ v s B`: $v$ roots a complete forcing tree of $\Psi_I$ of size $\le s$ whose variables avoid $B$.
--   * $\mathrm{Pois1}(x,\lambda)$ (Definition 2.2), `pois1Prob`: $\mathrm{Pois}(\lambda n)$ clauses i.i.d. uniform among the proper $k$-clauses with exactly one $x$-true literal. A uniform such clause is a uniform forced variable $v$ with a uniform $(k-1)$-subset of the others and the signs that make $v$ the unique true literal, so by Poisson superposition this has the clause-multiset law of the paper's independent $\mathrm{Pois}(\lambda)$ counts per variable.
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Definition 2.1 (printed p. 11, PDF 13), Lemma 2.7 (p. 12, PDF 14), Definition 3.1 (p. 14, PDF 16), Definition 2.2 (p. 11), Definition 7.2 and §7.1 constants (p. 53, PDF 55)

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_Model

noncomputable section

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-! # Factor graphs, local tree structure, regularity and complete forcing trees

Wang, Yin, Yu, Zhang (2026), arXiv:2611.05981: Definition 2.1 (p. 11), Lemma 2.7 (p. 12),
Definition 3.1 (p. 14), Definition 7.2 and the constants `ρ`, `η` (p. 53). -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The factor graph `G(Φ)` (Definition 2.1): the bipartite graph on variables `V` and clause
indices, joining each clause to the variables of its scope. Repeated clauses are distinct
vertices. -/
def factorGraph (Φ : GFormula V) : SimpleGraph (V ⊕ Fin Φ.length) :=
  SimpleGraph.fromRel fun a b =>
    ∃ (v : V) (j : Fin Φ.length), a = Sum.inl v ∧ b = Sum.inr j ∧ (Φ.get j v).isSome

/-- `a` is within factor-graph distance `d` of `b` (`false` when they are not connected). -/
def withinDist (Φ : GFormula V) (a b : V ⊕ Fin Φ.length) (d : ℕ) : Prop :=
  (factorGraph Φ).Reachable a b ∧ (factorGraph Φ).dist a b ≤ d

/-- The variables of the ball `B_r(Φ, v)`: within factor-graph distance `2r` of `v`. -/
def ballVars (Φ : GFormula V) (v : V) (r : ℕ) : Finset V :=
  Finset.univ.filter fun u => withinDist Φ (Sum.inl v) (Sum.inl u) (2 * r)

/-- The clause positions of the ball `B_r(Φ, v)`: within factor-graph distance `2r` of `v`
(being at odd distance, they are within `2r − 1`). -/
def ballIdx (Φ : GFormula V) (v : V) (r : ℕ) : Finset (Fin Φ.length) :=
  Finset.univ.filter fun j => withinDist Φ (Sum.inl v) (Sum.inr j) (2 * r)

/-- The ball `B_r(Φ, v)` (Definition 2.1, the radius-`2r` ball around `v` in `G(Φ)`) as a formula
on the same variable type: its clauses are those of the ball; every variable of a ball clause lies
in the ball. Variables outside the ball carry no clause of this formula. -/
def ballF (Φ : GFormula V) (v : V) (r : ℕ) : GFormula V := subF Φ (ballIdx Φ v r)

/-- `B_r(Φ, v)` is a tree: the factor graph of the ball formula has no cycle (all its clauses are
connected to `v`; variables outside the ball are isolated there). -/
def BallIsTree (Φ : GFormula V) (v : V) (r : ℕ) : Prop := (factorGraph (ballF Φ v r)).IsAcyclic

/-- The degree of the variable `u` in `Φ`: the number of clause positions containing it. -/
def degree (Φ : GFormula V) (u : V) : ℕ :=
  (Finset.univ.filter fun j : Fin Φ.length => (Φ.get j u).isSome).card

/-- `v` is `(r, D)`-locally tree-structured in `Φ` (Lemma 2.7): `B_r(Φ, v)` is a tree and every
variable in it has degree at most `D` in `Φ`. -/
def LocallyTree (Φ : GFormula V) (v : V) (r D : ℕ) : Prop :=
  BallIsTree Φ v r ∧ ∀ u ∈ ballVars Φ v r, degree Φ u ≤ D

/-- `ρ = k^{−100 ⌈(ln k)^6⌉}` (§7.1, p. 53). -/
def rho (k : ℕ) : ℝ := 1 / (k : ℝ) ^ (100 * ⌈Real.log k ^ 6⌉₊)

/-- `η = (ln k)^{10}/(64 k)` (§7.1, p. 53). -/
def etaC (k : ℕ) : ℝ := Real.log k ^ 10 / (64 * k)

/-- `LT(Φ)` (Definition 7.2(i)) with degree cutoff `D` (the paper's `D_k`): at least `(1 − η)n`
variables are `(2k + 4, D)`-locally tree-structured. -/
def LT {n : ℕ} (k D : ℕ) (Φ : GFormula (Fin n)) : Prop :=
  (1 - etaC k) * n ≤ ((Finset.univ.filter fun v => LocallyTree Φ v (2 * k + 4) D).card : ℝ)

/-- `LS(Φ)` (Definition 7.2(ii)): `|{C ∈ Φ : vbl(C) ⊆ A}| < 2|A|/k` for every `A ⊆ [n]` with
`0 < |A| ≤ ρ n` (clauses counted with multiplicity). -/
def LS {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n)) : Prop :=
  ∀ A : Finset (Fin n), 0 < A.card → (A.card : ℝ) ≤ rho k * n →
    ((Finset.univ.filter fun j : Fin Φ.length => vbl (Φ.get j) ⊆ A).card : ℝ) < 2 * A.card / k

/-- `Reg(Φ) = LT(Φ) ∩ LS(Φ)` (Definition 7.2) with degree cutoff `D`. -/
def Reg {n : ℕ} (k D : ℕ) (Φ : GFormula (Fin n)) : Prop := LT k D Φ ∧ LS k Φ

/-- `C` forces `v` under `σ`: `sat_σ(C) = {v}` (Definition 3.1). -/
def Forces (σ : V → Bool) (C : GClause V) (v : V) : Prop := satSet σ C = {v}

/-- A forcing tree in `Ψ` under `σ` (Definition 3.1): a variable-rooted subtree of the factor graph
in which every clause forces its parent variable and has a unique child variable. Clauses are
positions of `Ψ`; `parent c`, `child c` are the tree neighbours of clause `c`; `depth` certifies
that following parents strictly decreases depth, so the structure is a rooted tree. -/
structure ForcingTree (Ψ : GFormula V) (σ : V → Bool) where
  root : V
  vars : Finset V
  cls : Finset (Fin Ψ.length)
  parent : Fin Ψ.length → V
  child : Fin Ψ.length → V
  depth : V → ℕ
  root_mem : root ∈ vars
  forces : ∀ c ∈ cls, Forces σ (Ψ.get c) (parent c)
  parent_mem : ∀ c ∈ cls, parent c ∈ vars
  child_mem : ∀ c ∈ cls, child c ∈ vars
  child_vbl : ∀ c ∈ cls, child c ∈ vbl (Ψ.get c)
  depth_root : depth root = 0
  depth_child : ∀ c ∈ cls, depth (child c) = depth (parent c) + 1
  unique_parent : ∀ u ∈ vars, u ≠ root → ∃! c, c ∈ cls ∧ child c = u

namespace ForcingTree

variable {Ψ : GFormula V} {σ : V → Bool}

/-- The tree lies in the sub-formula `Ψ_I` of `Ψ` (its clause positions are in `I`) and is
complete there: every clause of `Ψ_I` forcing a variable of the tree is a child clause of that
variable. -/
def CompleteIn (T : ForcingTree Ψ σ) (I : Finset (Fin Ψ.length)) : Prop :=
  T.cls ⊆ I ∧ ∀ v ∈ T.vars, ∀ c ∈ I, Forces σ (Ψ.get c) v → c ∈ T.cls ∧ T.parent c = v

/-- The size of a forcing tree: the number of its variables. -/
def size (T : ForcingTree Ψ σ) : ℕ := T.vars.card

end ForcingTree

/-- `v` roots a complete forcing tree of the sub-formula `Ψ_I` (positions `I` of `Ψ`) under `σ`,
of size at most `s`, whose variables avoid `B`. -/
def HasSmallCFT (Ψ : GFormula V) (I : Finset (Fin Ψ.length)) (σ : V → Bool) (v : V) (s : ℝ)
    (B : Finset V) : Prop :=
  ∃ T : ForcingTree Ψ σ, T.root = v ∧ T.CompleteIn I ∧ (T.size : ℝ) ≤ s ∧ Disjoint T.vars B

/-- `Pois1(x, λ)` (Definition 2.2) as a law on clause lists: `Pois(λ n)` independent clauses, each
uniform among the proper `k`-clauses with exactly one true literal under `x`. (A uniform such clause
is a uniform forced variable `v` with a uniform `(k−1)`-set of other variables and the signs making
`v` the unique true literal; by Poisson superposition the per-variable `Pois(λ)` counts of the
paper give the same clause multiset law.) -/
def pois1Prob (n k : ℕ) (x : Fin n → Bool) (lam : ℝ) (P : List (OAI.FixedClauseThreshold.ProperClause n k) → Prop) : ℝ :=
  poisProb (oneTrueClauses x) (lam * n) P

end KSATSingleFlip.Connect



-- Prove2me | Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Graph
-- name    : MTWalkSAT3CNF_TwoOcc_Supplement_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:56:46.284345+00:00
-- url     : https://prove2.me/theorems/b7855926-274c-4472-9001-19902692ed94
-- title:
--   Sorted adjacency eigenvalues and computable graph families
-- statement:
--   A finite simple graph is represented by Mathlib's graph on $\operatorname{Fin}N$. Its real adjacency matrix has eigenvalues $\lambda_1\ge\cdots\ge\lambda_N$, listed with multiplicity. The graph conditions used in §6 are
--
--   $$N>0,\quad G\text{ connected and }102\text{-regular},\quad\lambda_1=102,\quad|\lambda_i|<21\ (2\le i\le N).$$
--
--   A finite adjacency matrix is encoded by a pair of natural numbers: its order and its row-major adjacency bits. Decoding symmetrizes the relation and removes the diagonal, so every code yields a simple graph and every finite simple graph can be encoded. An explicit expander family is a computable function from natural indices to these pairs whose decoded graphs satisfy the displayed conditions and whose vertex counts tend to infinity. This retains an actual algorithmic enumeration, without imposing an efficiency bound.
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), §6.1, Lemma 6.2 and its proof, p. 35; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Mathlib

set_option autoImplicit false

namespace MTWalkSAT3CNF.TwoOcc.Supplement

/-- Eigenvalues of the real adjacency matrix, decreasingly, including multiplicity. -/
noncomputable def adjacencyEigenvalues {N : ℕ} (G : SimpleGraph (Fin N)) : Fin N → ℝ := by
  classical
  have h : (G.adjMatrix ℝ).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, SimpleGraph.adj_comm]
  exact fun i => h.eigenvalues₀ ⟨i.val, by simp⟩

/-- Precisely the graph conditions used in §6; no runtime condition is bundled here. -/
def GoodGraph {N : ℕ} (G : SimpleGraph (Fin N)) : Prop :=
  0 < N ∧ G.Connected ∧
  (∀ v, (Set.ncard (G.neighborSet v)) = 102) ∧
  (∀ i : Fin N, i.val = 0 → adjacencyEigenvalues G i = 102) ∧
  (∀ i : Fin N, 0 < i.val → |adjacencyEigenvalues G i| < 21)

/-- Finite simple graph decoded from (vertex count, row-major adjacency bits).
Symmetrization and removal of the diagonal make every code a simple graph. -/
def graphOfCode (c : ℕ × ℕ) : SimpleGraph (Fin c.1) where
  Adj u v := u ≠ v ∧ (c.2.testBit (u.val*c.1+v.val) = true ∨
    c.2.testBit (v.val*c.1+u.val) = true)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A computable output code gives a finite adjacency matrix, with no efficiency requirement. -/
def ExplicitExpanderFamily (f : ℕ → ℕ × ℕ) : Prop :=
  Computable f ∧ (∀ j, GoodGraph (graphOfCode (f j))) ∧
  Filter.Tendsto (fun j => (f j).1) Filter.atTop Filter.atTop

end MTWalkSAT3CNF.TwoOcc.Supplement



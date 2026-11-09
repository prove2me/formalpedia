-- Prove2me | Definitions.Def_SuperRamanujan227_Main_ConfigurationModel
-- name    : SuperRamanujan227_Main_ConfigurationModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:31:53.211763+00:00
-- url     : https://prove2.me/theorems/e028c235-e4de-4d08-a263-88ac4f554421
-- title:
--   Configuration-model adjacency matrix $A_P=U^{\mathsf T}PMP^{\mathsf T}U$
-- statement:
--   Let $N=nd$ and label the half-edges (ports) $0,\dots,N-1$, port $p$ belonging to vertex $\lfloor p/d\rfloor$. The **up matrix** $U\in\mathbb R^{N\times n}$ acts by $Ux=x\otimes\mathbf 1_d$. Let $M$ be the adjacency matrix of the fixed perfect matching of the ports pairing $2i$ with $2i+1$ (for $N$ even); no port is paired with itself. For an $N\times N$ permutation matrix $P$ set
--   $$A_P=U^{\mathsf T}PMP^{\mathsf T}U\qquad\text{(Eq. (24))}.$$
--   For $P$ uniformly random, $PMP^{\mathsf T}$ is a uniformly random perfect matching of the $nd$ half-edges, and $A_P$ is the adjacency matrix of the configuration-model $d$-regular multigraph of Definition 5.2 (self-loops and parallel edges allowed, a loop contributing $2$ to its diagonal entry).
--
--   This is the random model behind the proof of Theorem 1.1; it is not a hypothesis of any statement.
--
--   **Formalization Note** The matrix is defined over $\mathbb R$; the vertex-major port order matches $x\otimes\mathbf 1_d$.
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, Definition 5.2 and Eq. (24), p. 17

import Mathlib

namespace SuperRamanujan227.Main

/-- The `N × n` up matrix `U`, `N = nd` (p. 17): `U x = x ⊗ 1_d`. Half-edge (port) `p` belongs to
vertex `⌊p / d⌋`, so vertex `v` owns ports `vd, …, vd + d - 1`. -/
def upMatrix (n d : ℕ) : Matrix (Fin (n * d)) (Fin n) ℝ :=
  fun p v => if p.val / d = v.val then 1 else 0

/-- The adjacency matrix `M` of a fixed perfect matching on `N` ports (p. 17), pairing port `2i`
with port `2i + 1`; no port is matched to itself. It is a perfect matching when `N` is even. -/
def matchingMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun p q => if p.val / 2 = q.val / 2 ∧ p ≠ q then 1 else 0

/-- Eq. (24), p. 17: the configuration-model adjacency matrix `A_P = Uᵀ P M Pᵀ U` for the
permutation matrix `P` of `σ`; for `σ` uniform this is the configuration model of
Definition 5.2 (a uniformly random perfect matching of the `nd` half-edges). -/
noncomputable def configAdj (n d : ℕ) (σ : Equiv.Perm (Fin (n * d))) :
    Matrix (Fin n) (Fin n) ℝ :=
  (upMatrix n d).transpose * σ.permMatrix ℝ * matchingMatrix (n * d) *
    (σ.permMatrix ℝ).transpose * upMatrix n d

end SuperRamanujan227.Main



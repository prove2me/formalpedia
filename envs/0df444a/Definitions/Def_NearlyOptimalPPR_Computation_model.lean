-- Prove2me | Definitions.Def_NearlyOptimalPPR_Computation_model
-- name    : NearlyOptimalPPR_Computation_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:34:39.824075+00:00
-- url     : https://prove2.me/theorems/4399145b-3a41-46f1-933b-01440752c630
-- title:
--   Finite graphs, isolate-safe PPR, and absolute ACL error
-- statement:
--   Let $G=(V,E)$ be a finite simple unweighted undirected graph, $s\in V$ a seed, $d_v$ its degrees, $D=\operatorname{diag}(d)$, $A$ its adjacency matrix, and $M=D-(1-\alpha)A$. The transition matrix is column-oriented, $AD^{-1}$. The positive-degree induced graph is used for all matrix inverses. For a nonisolated seed, $\pi_s$ is the published PageRank vector on that subtype extended by zero at isolated vertices; for an isolated seed, $\pi_s=e_s$.
--
--   For real $\alpha\in(0,1)$ and $0<\varepsilon\le1$, an arbitrary estimate $p:V\to\mathbb R$ satisfies the ACL guarantee precisely when
--
--   $$|p(v)-\pi_s(v)|\le\varepsilon d_v\qquad(v\in V).$$
--
--   The residual of a potential $z$ is $e_s-Mz$, its output is $\alpha Dz$, and root pruning replaces $x_v$ by $\max\{x_v-3q/8,0\}$. The Green operator applies the inverse of the positive-degree principal matrix and extends by zero. No nonnegative-output or residual-representation condition is bundled into ACL.
--
--   Algorithm inputs use vertices $\{0,\ldots,n-1\}$ and duplicate-free adjacency lists in any order; lists may be empty. Explicit output is a finite list of labeled real values: duplicate labels add and omitted labels mean zero. The mathematical envelope is $C\varepsilon^{-1}\exp(c\sqrt{\log(2/\varepsilon)\log\log(4/\varepsilon)})$, the depth is $\lfloor\sqrt{\log(2/\varepsilon)/\log\log(4/\varepsilon)}\rfloor$, $\kappa_j=\ell-j+3$, and $q_0=\varepsilon/(32\kappa_0)$. These are mathematical specifications rather than free machine instructions. The star on $L+1$ vertices has center zero.
--
--   These definitions fix the objects shared by the target and its residual, recursive, and output-size statements.
--
--   Differences from the source:
--   - encoding: finite adjacency-list graphs and matrix identities on positive-degree vertices → Fin n adjacency-list inputs and a positive-degree subtype, with exact isolated-seed output; reason: every finite labeled instance is represented and singular full-graph inverses are avoided
--   - encoding: an explicit sparse output vector → a finite labeled list with omitted entries zero and repeated labels added; reason: every emitted entry has a charge and no dense scan is supplied
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Definition 1.1 p.2; §2 p.4; §4.1 pp.17–19

import Mathlib
import Definitions.Def_LocalPush_PageRank

set_option autoImplicit false

open Finset Matrix

noncomputable section

namespace NearlyOptimalPPR.Computation

/-! Li, Xu, Yang, Zhou, STOC 2027 submission #884 (October 2026),
Definition 1.1 p.2 and §2 p.4. Matrix identities use the positive-degree
subtype, and isolated sources are returned exactly. -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Positive-degree vertices. No condition is imposed on the other vertices. -/
abbrev PositiveVertices (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {v : V // 0 < G.degree v}

/-- The induced graph used for matrix inverses. -/
def positiveGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph (PositiveVertices G) := G.induce {v | 0 < G.degree v}

/-- Extend a vector on positive-degree vertices by zero. -/
noncomputable def extendPositive (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : PositiveVertices G → ℝ) : V → ℝ :=
  fun v => if h : 0 < G.degree v then u ⟨v, h⟩ else 0

/-- The source's PPR vector, using the published transition-matrix definition
on the positive-degree subtype. The isolated-source branch is explicit. -/
noncomputable def ppr (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (s : V) : V → ℝ := by
  classical
  exact if h : 0 < G.degree s then
    extendPositive G (LocalPush.pr (positiveGraph G) α (LocalPush.e ⟨s, h⟩))
  else LocalPush.e s

/-- Applying the inverse of M on positive-degree vertices only. -/
noncomputable def green (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (r : V → ℝ) : V → ℝ := by
  classical
  let M : Matrix (PositiveVertices G) (PositiveVertices G) ℝ :=
    (LocalPush.Lα G α).submatrix Subtype.val Subtype.val
  exact extendPositive G (M⁻¹ *ᵥ (fun v : PositiveVertices G => r v))

/-- The output associated with a potential z. -/
def potentialOutput (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (z : V → ℝ) : V → ℝ := fun v => α * LocalPush.deg G v * z v

/-- The paper's absolute, coordinatewise ACL error guarantee. In particular,
nonnegativity and a residual representation are not clauses of this predicate. -/
noncomputable def ACL (G : SimpleGraph V) [DecidableRel G.Adj]
    (α ε : ℝ) (s : V) (p : V → ℝ) : Prop :=
  ∀ v, |p v - ppr G α s v| ≤ ε * LocalPush.deg G v

/-- The residual e_s - M z. -/
def residual (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (s : V) (z : V → ℝ) : V → ℝ :=
  LocalPush.e s - LocalPush.Lα G α *ᵥ z

/-- Pruning is part of the algorithm's return rule. -/
def prune (q : ℝ) (x : V → ℝ) : V → ℝ := fun v => max (x v - 3 * q / 8) 0

/-- An adjacency-list input, allowing empty lists. These are exactly the lists
of a finite simple unweighted undirected graph, in arbitrary neighbor order. -/
structure InputGraph (n : ℕ) where
  graph : SimpleGraph (Fin n)
  adjacencyDecidable : DecidableRel graph.Adj
  neighbors : Fin n → List (Fin n)
  nodup : ∀ v, (neighbors v).Nodup
  correct : ∀ v u, u ∈ neighbors v ↔ graph.Adj v u

attribute [instance] InputGraph.adjacencyDecidable

/-- An explicit output is a list of labeled values. Omitted vertices mean zero;
duplicate labels are added. Emitting any list entry has positive charged work. -/
abbrev SparseOutput := List (ℤ × ℝ)

def outputVector {n : ℕ} (o : SparseOutput) : Fin n → ℝ :=
  fun v => (o.map fun a => if a.1 = (v.val : ℤ) then a.2 else 0).sum

/-- The quantitative envelope on p.18, with absolute C,c quantified by theorems. -/
noncomputable def envelope (C c ε : ℝ) : ℝ :=
  C * (1 / ε) * Real.exp
    (c * Real.sqrt (Real.log (2 / ε) * Real.log (Real.log (4 / ε))))

/-- The mathematical depth in Lemma 4.5. This is a specification, not a RAM
instruction or an uncharged parameter-preparation operation. -/
noncomputable def balancedDepth (ε : ℝ) : ℕ :=
  ⌊Real.sqrt (Real.log (2 / ε) / Real.log (Real.log (4 / ε)))⌋₊

def kappa (ℓ j : ℕ) : ℕ := ℓ - j + 3

def rootThreshold (ε : ℝ) (ℓ : ℕ) : ℝ := ε / (32 * (kappa ℓ 0 : ℝ))

/-- A star with L leaves, centered at vertex zero. -/
def star (L : ℕ) : SimpleGraph (Fin (L + 1)) where
  Adj u v := u ≠ v ∧ (u.val = 0 ∨ v.val = 0)
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

end NearlyOptimalPPR.Computation



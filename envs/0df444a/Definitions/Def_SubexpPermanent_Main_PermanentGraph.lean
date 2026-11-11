-- Prove2me | Definitions.Def_SubexpPermanent_Main_PermanentGraph
-- name    : SubexpPermanent_Main_PermanentGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:01:27.026981+00:00
-- url     : https://prove2.me/theorems/4223904e-8b0c-4b33-a598-cdb11431fb50
-- title:
--   The bipartite graph of a nonnegative matrix: the edge set $E$, perfect matchings, incidence vectors, the polytope $B$, the weights $e^y$, $Z(e^y)$, $\mu_y$ and vertex sums
-- statement:
--   Let $A$ be a real $n\times n$ matrix. Its rows form the part $L$ and its columns the part $R$ of a bipartite graph. A **perfect matching of positive entries** is a permutation $\sigma$ with $A_{k\sigma(k)}>0$ for every row $k$. The edge set $E$ consists of the pairs $(i,j)$ with $A_{ij}>0$ that lie in at least one such perfect matching (edges in no perfect matching are removed), and $G=(L\cup R,E)$ is the graph in which row $i$ and column $j$ are adjacent iff $(i,j)\in E$. Vectors in $\mathbb R^E$ are indexed by the edges of $E$. Further notation:
--   - a **perfect matching using $E$** is a permutation $\sigma$ with $(k,\sigma(k))\in E$ for all $k$, and $1_\sigma\in\{0,1\}^E$ is its **incidence vector**;
--   - $B$ is the set of nonnegative matrices supported on $E$ whose row and column sums are all one, identified with their vectors of entries on $E$;
--   - $\log A\in\mathbb R^E$ has entries $\log A_e$;
--   - for $y\in\mathbb R^E$, $e^y$ is the weight $e^{y_e}$ on each edge of $E$, extended by zero outside $E$;
--   - $Z(e^y)=Z_G(e^y)$ is the matching partition function of $G$, and $\mu_{y,e}$ the probability that $e\in M$ for $M\sim\nu_{G,e^y}$;
--   - $\sum_{e\ni v}e^{x_e}$ is the total weight at a vertex $v$.
--
--   **Formalization Note.** Rows are `Sum.inl i` and columns `Sum.inr j` in `Fin n ⊕ Fin n`; $\mathbb R^E$ is `Edges A → ℝ`, where `Edges A` is the subtype of pairs in $E$. The matching quantities are those of the shared definition `Matchings`, applied to `bipGraph A` with weights `expWeight A y`.
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 3 (§2.1), p. 12 (§4.1), p. 20 (§6)

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Matchings

namespace SubexpPermanent.Main

/-! # The bipartite graph of a nonnegative matrix (Kudria–Luo–Majid, §2.1 p. 3, §4.1 p. 12, §6 p. 20)

For a real `n × n` matrix `A`, rows are the vertices `Sum.inl i` (the part `L`) and columns the
vertices `Sum.inr j` (the part `R`). `E` is the set of positive entries `(i, j)` that lie in at
least one perfect matching of positive entries. Edge-indexed vectors (`ℝ^E`) are functions on the
subtype `Edges A`.
-/

open Classical

variable {n : ℕ}

/-- `σ` is a perfect matching of the positive entries of `A`: `A k (σ k) > 0` for every row `k`. -/
def IsPosPerm (A : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k, 0 < A k (σ k)

/-- `(i, j) ∈ E`: the entry is positive and lies in some perfect matching of positive entries. -/
def InE (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n × Fin n) : Prop :=
  0 < A p.1 p.2 ∧ ∃ σ : Equiv.Perm (Fin n), IsPosPerm A σ ∧ σ p.1 = p.2

/-- The edge set `E` as a type: `ℝ^E` is `Edges A → ℝ`. -/
def Edges (A : Matrix (Fin n) (Fin n) ℝ) : Type :=
  {p : Fin n × Fin n // InE A p}

noncomputable instance (A : Matrix (Fin n) (Fin n) ℝ) : Fintype (Edges A) :=
  Subtype.fintype _

noncomputable instance (A : Matrix (Fin n) (Fin n) ℝ) : DecidableEq (Edges A) :=
  fun a b => decEq a b

/-- A perfect matching using edges of `E` (a permutation whose every pair `(k, σ k)` is in `E`). -/
def IsPerfMatching (A : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k, InE A (k, σ k)

/-- The incidence vector in `ℝ^E` of the perfect matching `σ`: one on the edges `(k, σ k)`. -/
noncomputable def incVec (A : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) : Edges A → ℝ :=
  fun e => if σ e.1.1 = e.1.2 then 1 else 0

/-- `B`: nonnegative matrices supported on `E` with every row and column sum equal to one,
identified with their vectors of entries on `E`. -/
def polytopeB (A : Matrix (Fin n) (Fin n) ℝ) : Set (Edges A → ℝ) :=
  {P | (∀ e, 0 ≤ P e) ∧
    (∀ i : Fin n, ∑ e ∈ Finset.univ.filter (fun e : Edges A => e.1.1 = i), P e = 1) ∧
    (∀ j : Fin n, ∑ e ∈ Finset.univ.filter (fun e : Edges A => e.1.2 = j), P e = 1)}

/-- `log A` as a vector on `E` (entries on `E` are positive). -/
noncomputable def logA (A : Matrix (Fin n) (Fin n) ℝ) : Edges A → ℝ :=
  fun e => Real.log (A e.1.1 e.1.2)

/-- Adjacency of the bipartite graph `G = (L ∪ R, E)`. -/
def bipAdj (A : Matrix (Fin n) (Fin n) ℝ) : Fin n ⊕ Fin n → Fin n ⊕ Fin n → Prop
  | Sum.inl i, Sum.inr j => InE A (i, j)
  | Sum.inr j, Sum.inl i => InE A (i, j)
  | _, _ => False

/-- The bipartite graph `G = (L ∪ R, E)` of `A`: row `i` and column `j` are adjacent iff
`(i, j) ∈ E`. -/
def bipGraph (A : Matrix (Fin n) (Fin n) ℝ) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj := bipAdj A
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp_all [bipAdj]⟩
  loopless := ⟨by
    intro u h
    cases u <;> simp_all [bipAdj]⟩

/-- The edge `(i, j) ∈ E` as an unordered pair of vertices `{row i, column j}`. -/
def toSym2 {A : Matrix (Fin n) (Fin n) ℝ} (e : Edges A) : Sym2 (Fin n ⊕ Fin n) :=
  s(Sum.inl e.1.1, Sum.inr e.1.2)

/-- `e^y` on the edges of `E`, extended by zero outside them (the paper's convention for
exponentiating an edge vector). -/
noncomputable def expWeight (A : Matrix (Fin n) (Fin n) ℝ) (y : Edges A → ℝ) :
    Sym2 (Fin n ⊕ Fin n) → ℝ :=
  fun s => ∑ e : Edges A, if toSym2 e = s then Real.exp (y e) else 0

/-- `Z(e^y) = Z_G(e^y)`: the matching partition function of `G` at weights `e^y`. -/
noncomputable def ZA (A : Matrix (Fin n) (Fin n) ℝ) (y : Edges A → ℝ) : ℝ :=
  matchingZ (bipGraph A) (expWeight A y) Finset.univ

/-- `μ_y`: the vector of edge probabilities `μ_{y,e} = Pr(e ∈ M)`, `M ∼ ν_{G,e^y}`. -/
noncomputable def edgeProbA (A : Matrix (Fin n) (Fin n) ℝ) (y : Edges A → ℝ) : Edges A → ℝ :=
  fun e => edgeProb (bipGraph A) (expWeight A y) Finset.univ (toSym2 e)

/-- The edge `e` is incident to the vertex `v` (row `e.1.1` or column `e.1.2`). -/
def Incident {A : Matrix (Fin n) (Fin n) ℝ} (e : Edges A) (v : Fin n ⊕ Fin n) : Prop :=
  v = Sum.inl e.1.1 ∨ v = Sum.inr e.1.2

/-- `∑_{e ∋ v} e^{x_e}`: the total weight at the vertex `v` under weights `e^x`. -/
noncomputable def vertexSum (A : Matrix (Fin n) (Fin n) ℝ) (x : Edges A → ℝ)
    (v : Fin n ⊕ Fin n) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : Edges A => Incident e v), Real.exp (x e)

end SubexpPermanent.Main



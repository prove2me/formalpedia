-- Prove2me | Definitions.Def_HZFixp_Main_ReciprocalVI
-- name    : HZFixp_Main_ReciprocalVI
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:51:22.02033+00:00
-- url     : https://prove2.me/theorems/926780ac-d271-4182-9c21-ad23bfe20a3d
-- title:
--   Definition 3.3 — reciprocal graphs, the field (2), the box conditions (3) and Reciprocal VI
-- statement:
--   A **reciprocal graph** is a directed multigraph on nodes $i$ with rational intervals $[a_i,b_i] \subset (0,\infty)$ and edges $e : i \to j$ carrying ratios $\lambda_e > 0$; the edges are listed explicitly and parallel edges contribute independently. For node values $r$, edge $e : i\to j$ contributes
--   $$I_e(r) = \frac{\lambda_e}{r_i + \lambda_e r_j}$$
--   at $i$ and $-I_e(r)$ at $j$, so the **field** at $i$ is $G_i(r) = \sum_{e : i \to j} I_e(r) - \sum_{e : j \to i} I_e(r)$ (2). The **box conditions** (3) require $r_i \in [a_i,b_i]$ and
--   $$G_i(r) \le 0 \ \text{if } r_i = a_i,\qquad G_i(r) = 0 \ \text{if } a_i < r_i < b_i,\qquad G_i(r) \ge 0 \ \text{if } r_i = b_i .$$
--
--   An instance of **Reciprocal VI** (Definition 3.3) is such a graph with $1 \le a_i < b_i$ for all nodes, $0 < \lambda_e \le a_i$ for every edge $e : i \to j$, an integer $M \ge 1$, and disjoint designated pairs $(A_j, D_j)$, $j \in [d]$, each with a designated ratio-one edge $A_j \to D_j$, the intervals of $A_j$ and $D_j$ being $[M,2M]$ and $[2M,3M]$; and every solution of (3) satisfies $r_{A_j} + r_{D_j} = 4M$. All numerators and denominators of endpoints and ratios, and $M$, are written in **unary**. A solution is a vector $z \in [1,2]^d$ that extends to a solution $r$ of (3) with $r_{A_j} = M z_j$.
--
--   Theorem 3.4 shows Reciprocal VI is FIXP-hard; the market of §3.4 turns it into an HZ market.
--
--   **Formalization Note.** Nodes are the $0$-based positions of the interval list; an edge is a triple (tail, head, $\lambda_e$); a designated pair is (A, D, position of its designated edge in the edge list), and disjointness means that the list of all $A_j, D_j$ has no repetition. The encoding writes every number in unary (a framed run of ones; a rational as the positive and negative parts of its reduced numerator and its denominator); only the lengths of the three lists are binary, which changes lengths by at most a constant factor since the lists are written out. `BoxCond a b r G` is (3) at one node.
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 6–7 (PDF 8–9), (2), (3), Definition 3.3 and the paragraph before it

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch

namespace HZFixp.Main

open OnlineCRS.Combine FixpReciprocal

/-- **Unary encoding of a natural number:** `n` ones, framed (Reciprocal VI: "numerators and
denominators encoded in unary", "a unary integer `M`"). Its length is `2n + 1`. -/
def uNat (n : ℕ) : List Sym := frame (List.replicate n 1)

theorem uNat_prefixFree : PrefixFree uNat := fun a b s t h => by
  obtain ⟨h1, h2⟩ := frame_append_inj h
  exact ⟨by simpa using congrArg List.length h1, h2⟩

/-- **Unary encoding of a rational number:** the positive part and the negative part of its reduced
numerator, then its denominator, each in unary. -/
def uRat (q : ℚ) : List Sym := uNat q.num.toNat ++ uNat (-q.num).toNat ++ uNat q.den

theorem uRat_prefixFree : PrefixFree uRat := by
  intro a b s t h
  simp only [uRat, List.append_assoc] at h
  obtain ⟨h1, h⟩ := uNat_prefixFree h
  obtain ⟨h2, h⟩ := uNat_prefixFree h
  obtain ⟨h3, h⟩ := uNat_prefixFree h
  refine ⟨Rat.ext ?_ h3, h⟩
  rw [← Int.toNat_sub_toNat_neg a.num, ← Int.toNat_sub_toNat_neg b.num, h1, h2]

/-- The data of a reciprocal graph with designated pairs: node intervals `[a_i, b_i]` (node `i` is
the `i`-th entry, `0`-based), the explicit list of unit edges `(i, j, λ_e)` for `e : i → j` (parallel
edges are repeated entries), the integer `M`, and the designated pairs `(A_j, D_j, e_j)` with `e_j`
the position of the designated edge `A_j → D_j` in the edge list. -/
structure RVIData where
  /-- the intervals `(a_i, b_i)` -/
  intervals : List (ℚ × ℚ)
  /-- the edges `(tail, head, ratio)` -/
  edges : List (ℕ × ℕ × ℚ)
  /-- the scaling integer `M` -/
  M : ℕ
  /-- the designated pairs `(A_j, D_j, index of the designated edge)` -/
  pairs : List (ℕ × ℕ × ℕ)

/-- The number `k` of nodes. -/
def RVIData.k (D : RVIData) : ℕ := D.intervals.length

/-- The lower endpoint `a_i` of node `i` (`0` for an index that is not a node). -/
def RVIData.lo (D : RVIData) (i : ℕ) : ℚ := (D.intervals.getD i (0, 0)).1

/-- The upper endpoint `b_i` of node `i`. -/
def RVIData.hi (D : RVIData) (i : ℕ) : ℚ := (D.intervals.getD i (0, 0)).2

/-- **The reciprocal term (2)** of an edge `e : i → j` with ratio `λ_e`:
`I_e(r) = λ_e / (r_i + λ_e r_j)`. -/
noncomputable def edgeTerm (e : ℕ × ℕ × ℚ) (r : ℕ → ℝ) : ℝ :=
  (e.2.2 : ℝ) / (r e.1 + (e.2.2 : ℝ) * r e.2.1)

/-- **The field (2)** at node `i`: `G_i(r) = ∑_{e : i → j} I_e(r) − ∑_{e : j → i} I_e(r)`, each sum
over the edge list (parallel edges contribute independently). -/
noncomputable def RVIData.field (D : RVIData) (r : Fin D.k → ℝ) (i : Fin D.k) : ℝ :=
  ((D.edges.filter (fun e => e.1 == i.val)).map (fun e => edgeTerm e (lookup r))).sum -
    ((D.edges.filter (fun e => e.2.1 == i.val)).map (fun e => edgeTerm e (lookup r))).sum

/-- **The box condition (3)** of one node with interval `[a, b]`, value `r` and field `G`:
`r ∈ [a, b]`, and `G ≤ 0` if `r = a`, `G = 0` if `a < r < b`, `G ≥ 0` if `r = b`. -/
def BoxCond (a b r G : ℝ) : Prop :=
  a ≤ r ∧ r ≤ b ∧ (r = a → G ≤ 0) ∧ (a < r → r < b → G = 0) ∧ (r = b → 0 ≤ G)

/-- **A solution of the box conditions (3):** every node satisfies its box condition. -/
def RVIData.IsBoxSol (D : RVIData) (r : Fin D.k → ℝ) : Prop :=
  ∀ i : Fin D.k, BoxCond (D.lo i.val) (D.hi i.val) (r i) (D.field r i)

/-- **An instance of Reciprocal VI (Definition 3.3).** "A directed multigraph with intervals
`[a_i, b_i]` satisfying `1 ≤ a_i < b_i` for all nodes, ratios `0 < λ_e ≤ a_i` for every edge
`e : i → j`, a unary integer `M ≥ 1`, and disjoint designated pairs `(A_j, D_j)`, `j ∈ [d]`, each
with a designated ratio-one edge `A_j → D_j`. The intervals of `A_j` and `D_j` are `[M, 2M]` and
`[2M, 3M]`, respectively. Every solution to (3) satisfies `r_{A_j} + r_{D_j} = 4M` for each `j`."

Liu, Tao, Yan, *Settling the Complexity of Hylland–Zeckhauser Equilibria*, arXiv:2606.06317 (held
version later than v2, sha256 36e91522…af1c), p. 7, Definition 3.3; p. 6, (2) and (3).

**Formalization Note.** The pairs are disjoint when the list of all `A_j, D_j` has no repetition. -/
def RVIData.IsInstance (D : RVIData) : Prop :=
  (∀ iv ∈ D.intervals, 1 ≤ iv.1 ∧ iv.1 < iv.2) ∧
  (∀ e ∈ D.edges, e.1 < D.k ∧ e.2.1 < D.k ∧ 0 < e.2.2 ∧ e.2.2 ≤ D.lo e.1) ∧
  1 ≤ D.M ∧
  (∀ p ∈ D.pairs, p.1 < D.k ∧ p.2.1 < D.k ∧ D.edges[p.2.2]? = some (p.1, p.2.1, 1) ∧
    D.lo p.1 = D.M ∧ D.hi p.1 = 2 * D.M ∧ D.lo p.2.1 = 2 * D.M ∧ D.hi p.2.1 = 3 * D.M) ∧
  (D.pairs.flatMap (fun p => [p.1, p.2.1])).Nodup ∧
  ∀ r : Fin D.k → ℝ, D.IsBoxSol r →
    ∀ p ∈ D.pairs, lookup r p.1 + lookup r p.2.1 = 4 * (D.M : ℝ)

/-- Instances of Reciprocal VI. -/
def RVIInst : Type := {D : RVIData // D.IsInstance}

/-- Unary encoding of an interval. -/
def encInterval (iv : ℚ × ℚ) : List Sym := uRat iv.1 ++ uRat iv.2

/-- Unary encoding of an edge. -/
def encEdge (e : ℕ × ℕ × ℚ) : List Sym := uNat e.1 ++ uNat e.2.1 ++ uRat e.2.2

/-- Unary encoding of a designated pair. -/
def encPair (p : ℕ × ℕ × ℕ) : List Sym := uNat p.1 ++ uNat p.2.1 ++ uNat p.2.2

theorem encInterval_prefixFree : PrefixFree encInterval := by
  intro a b s t h
  simp only [encInterval, List.append_assoc] at h
  obtain ⟨h1, h⟩ := uRat_prefixFree h
  obtain ⟨h2, h⟩ := uRat_prefixFree h
  exact ⟨Prod.ext h1 h2, h⟩

theorem encEdge_prefixFree : PrefixFree encEdge := by
  intro a b s t h
  simp only [encEdge, List.append_assoc] at h
  obtain ⟨h1, h⟩ := uNat_prefixFree h
  obtain ⟨h2, h⟩ := uNat_prefixFree h
  obtain ⟨h3, h⟩ := uRat_prefixFree h
  exact ⟨Prod.ext h1 (Prod.ext h2 h3), h⟩

theorem encPair_prefixFree : PrefixFree encPair := by
  intro a b s t h
  simp only [encPair, List.append_assoc] at h
  obtain ⟨h1, h⟩ := uNat_prefixFree h
  obtain ⟨h2, h⟩ := uNat_prefixFree h
  obtain ⟨h3, h⟩ := uNat_prefixFree h
  exact ⟨Prod.ext h1 (Prod.ext h2 h3), h⟩

/-- **Unary encoding of a Reciprocal VI instance:** the intervals, the explicit edge list, `M` and
the designated pairs, every number (endpoint and ratio numerators and denominators, node indices,
`M`) in unary; only the lengths of the three lists are written in binary. -/
def encRVIData (D : RVIData) : List Sym :=
  fList encInterval D.intervals ++ fList encEdge D.edges ++ uNat D.M ++ fList encPair D.pairs

theorem encRVIData_injective : Function.Injective encRVIData := by
  rintro ⟨iv, ed, M, pr⟩ ⟨iv', ed', M', pr'⟩ h
  simp only [encRVIData, List.append_assoc] at h
  obtain ⟨h1, h⟩ := encInterval_prefixFree.fList h
  obtain ⟨h2, h⟩ := encEdge_prefixFree.fList h
  obtain ⟨h3, h⟩ := uNat_prefixFree h
  have h4 := encPair_prefixFree.fList.injective h
  simp_all

/-- The node `A_j` of designated pair `j`. -/
def RVIData.pairA (D : RVIData) (j : ℕ) : ℕ := (D.pairs.getD j (0, 0, 0)).1

/-- The node `D_j` of designated pair `j`. -/
def RVIData.pairD (D : RVIData) (j : ℕ) : ℕ := (D.pairs.getD j (0, 0, 0)).2.1

/-- **Reciprocal VI as a search problem (Definition 3.3).** Output: "A vector `z ∈ [1, 2]^d` that
extends to a solution of (3) with `r_{A_j} = M z_j`."

Liu, Tao, Yan, *Settling the Complexity of Hylland–Zeckhauser Equilibria*, arXiv:2606.06317 (held
version later than v2, sha256 36e91522…af1c), p. 7, Definition 3.3. -/
noncomputable def rviProblem : RealSearch where
  Inst := RVIInst
  enc := fun I => encRVIData I.1
  enc_injective := fun _ _ h => Subtype.ext (encRVIData_injective h)
  dim := fun I => I.1.pairs.length
  Sol := fun I => {z | (∀ j, z j ∈ Set.Icc (1 : ℝ) 2) ∧
    ∃ r : Fin I.1.k → ℝ, I.1.IsBoxSol r ∧
      ∀ j : Fin I.1.pairs.length, lookup r (I.1.pairA j.val) = (I.1.M : ℝ) * z j}

end HZFixp.Main



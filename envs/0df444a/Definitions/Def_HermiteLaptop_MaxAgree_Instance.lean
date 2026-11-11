-- Prove2me | Definitions.Def_HermiteLaptop_MaxAgree_Instance
-- name    : HermiteLaptop_MaxAgree_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:14:57.807378+00:00
-- url     : https://prove2.me/theorems/6b0452b0-0589-4346-83b6-7094b5c53606
-- title:
--   Weighted edge-labelled MaxAgree instances, the objective val, and the SDP family SDP(a) (§4.1, Eq. (23))
-- statement:
--   Let $V=\{1,\dots,n\}$. An **instance** is an edge-labelled simple undirected graph $G=(V,E)$ with $E=E_+\cup E_-$, $E_+\cap E_-=\emptyset$ (no loops, no parallel edges), and a weight $w_{ij}>0$ on every edge $\{i,j\}\in E$. For a clustering $\mathcal C$ of $V$ with $\mathcal C(i)$ the cluster of $i$, the **agreement objective** is
--   $$\mathrm{val}(\mathcal C)=\sum_{\{i,j\}\in E_+} w_{ij}\,\mathbf 1[\mathcal C(i)=\mathcal C(j)]+\sum_{\{i,j\}\in E_-} w_{ij}\,\mathbf 1[\mathcal C(i)\neq\mathcal C(j)].$$
--   For $a\in[-1/2,0]$ put $s^+_a(\rho)=(\rho-a)/(1-a)$ and $s^-_a(\rho)=(1-\rho)/(1-a)$. The semidefinite program $\mathrm{SDP}(a)$ maximizes
--   $$\sum_{\{i,j\}\in E_+} w_{ij}\,s^+_a(v_i\cdot v_j)+\sum_{\{i,j\}\in E_-} w_{ij}\,s^-_a(v_i\cdot v_j)$$
--   over vectors $v_1,\dots,v_n\in\mathbb R^n$ with $v_i\cdot v_i=1$ for all $i$ and $v_i\cdot v_j\ge a$ for all $i,j$. A feasible family is **optimal** when its objective is at least that of every feasible family. For $a=0$ the objective is $\sum_{E_+}w_{ij}\,v_i\cdot v_j+\sum_{E_-}w_{ij}(1-v_i\cdot v_j)$, the standard MaxAgree relaxation.
--
--   **Formalization Note.** `V = Fin n`; edges are `Sym2 (Fin n)` elements, non-diagonal; `w : Sym2 (Fin n) → ℝ` is positive on edges (values off edges are unused). A clustering is a labelling `C : Fin n → ℕ` (every partition of `V` is induced by one, and `val` depends only on the partition). SDP vectors are `v : Fin n → EuclideanSpace ℝ (Fin n)`. `Instance.val`, `sPlus`, `sMinus`, `Instance.sdpObj`, `SDPFeasible`, `Instance.SDPOptimal`.
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 26 (PDF 29), §4.1 and Eq. (23); p. 5 (PDF 8), §1.2.1

import Mathlib

open scoped RealInnerProductSpace

/-!
# Weighted MaxAgree instances, the objective `val`, and the SDP family `SDP(a)`

García-Soriano, Miyauchi, *Hermite Brings a Laptop*, arXiv:2609.35453 (held version, sha256
97504f90…), §4.1 p. 26 (PDF 29), Eq. (23); §1.2.1 p. 5 (simple graphs).

"Let G = (V, E) be an edge-labeled undirected graph with V = {1, . . . , n} and E = E+ ∪ E−, where
E+ ∩ E− = ∅. Each edge {i, j} ∈ E has a weight wij > 0 … val(C) = Σ_{{i,j}∈E+} wij 1[C(i) = C(j)]
+ Σ_{{i,j}∈E−} wij 1[C(i) ≠ C(j)]."

Conventions.
* `V = Fin n` (0-based labels `0, …, n-1` for the paper's `1, …, n`).
* An edge `{i, j}` is an element of `Sym2 (Fin n)`; `E₊`, `E₋` are finite sets of non-diagonal
  unordered pairs (a simple graph: no loops, no parallel edges), disjoint.
* The weight is a function `w : Sym2 (Fin n) → ℝ`, positive on every edge; its values off the
  edges are never used.
* A clustering `C` of `V` is encoded by a labelling `C : Fin n → ℕ`; `C(i) = C(j)` is `C i = C j`.
  Every partition of `V` is induced by some labelling, and two labellings inducing the same
  partition have the same `val`.
* SDP vectors are `v : Fin n → EuclideanSpace ℝ (Fin n)` (ambient dimension `n`, as on p. 13).
-/

namespace HermiteLaptop.MaxAgree

/-- A weighted, edge-labelled simple undirected graph on `V = Fin n` (§4.1). -/
structure Instance (n : ℕ) where
  /-- positive edges `E₊` -/
  Epos : Finset (Sym2 (Fin n))
  /-- negative edges `E₋` -/
  Eneg : Finset (Sym2 (Fin n))
  /-- edge weights `w_{ij}` -/
  w : Sym2 (Fin n) → ℝ
  /-- `E₊ ∩ E₋ = ∅` -/
  disjoint : Disjoint Epos Eneg
  /-- no loops in `E₊` (simple graph) -/
  pos_not_diag : ∀ e ∈ Epos, ¬ e.IsDiag
  /-- no loops in `E₋` (simple graph) -/
  neg_not_diag : ∀ e ∈ Eneg, ¬ e.IsDiag
  /-- `w_{ij} > 0` on every positive edge -/
  w_pos_pos : ∀ e ∈ Epos, 0 < w e
  /-- `w_{ij} > 0` on every negative edge -/
  w_pos_neg : ∀ e ∈ Eneg, 0 < w e

/-- `1[C(i) = C(j)]` for the edge `e = {i, j}` and the labelling `C`. -/
def sameInd {n : ℕ} (C : Fin n → ℕ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j => if C i = C j then 1 else 0, fun i j => by simp only [eq_comm]⟩

/-- The objective `val(C) = Σ_{E₊} w_{ij} 1[C(i)=C(j)] + Σ_{E₋} w_{ij} 1[C(i)≠C(j)]` (§4.1). -/
def Instance.val {n : ℕ} (I : Instance n) (C : Fin n → ℕ) : ℝ :=
  (∑ e ∈ I.Epos, I.w e * sameInd C e) + ∑ e ∈ I.Eneg, I.w e * (1 - sameInd C e)

/-- The inner product `v_i · v_j` of the SDP vectors at the edge `e = {i, j}`. -/
noncomputable def edgeInner {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j => ⟪v i, v j⟫, fun i j => real_inner_comm (v j) (v i)⟩

/-- `s⁺_a(ρ) = (ρ − a)/(1 − a)` (§4.1). -/
noncomputable def sPlus (a ρ : ℝ) : ℝ := (ρ - a) / (1 - a)

/-- `s⁻_a(ρ) = (1 − ρ)/(1 − a)` (§4.1). -/
noncomputable def sMinus (a ρ : ℝ) : ℝ := (1 - ρ) / (1 - a)

/-- The objective of `SDP(a)`, Eq. (23):
`Σ_{E₊} w_{ij} s⁺_a(v_i·v_j) + Σ_{E₋} w_{ij} s⁻_a(v_i·v_j)`. -/
noncomputable def Instance.sdpObj {n : ℕ} (I : Instance n) (a : ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ e ∈ I.Epos, I.w e * sPlus a (edgeInner v e)) +
    ∑ e ∈ I.Eneg, I.w e * sMinus a (edgeInner v e)

/-- Feasibility for `SDP(a)`, Eq. (23): `v_i · v_i = 1` and `v_i · v_j ≥ a` for all `i, j ∈ V`. -/
def SDPFeasible {n : ℕ} (a : ℝ) (v : Fin n → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ i, ⟪v i, v i⟫ = 1) ∧ ∀ i j, a ≤ ⟪v i, v j⟫

/-- `v` is an optimal solution of `SDP(a)`: feasible, with objective at least that of every
feasible family. -/
def Instance.SDPOptimal {n : ℕ} (I : Instance n) (a : ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin n)) : Prop :=
  SDPFeasible a v ∧ ∀ u : Fin n → EuclideanSpace ℝ (Fin n), SDPFeasible a u →
    I.sdpObj a u ≤ I.sdpObj a v

end HermiteLaptop.MaxAgree



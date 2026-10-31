-- Prove2me | Definitions.Def_ApproxNashSet_Algorithm
-- name    : ApproxNashSet_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:18:18.706738+00:00
-- url     : https://prove2.me/theorems/3d3f5854-b227-463a-8d83-5338bcd3c9f2
-- title:
--   A run of Algorithm 4.8 and its output $\mathcal X=\bigcap_i\bigcup_j(\mathrm{conv}\,\hat X^j_i+B_{\varepsilon_2})\cap\mathbb X$ (pp.7–11)
-- statement:
--   Algorithm 4.8 takes a convex game on a polytope $\mathbb X=\operatorname{conv}V$ and approximation levels $\varepsilon_1,\varepsilon_2$, and for every player $i$ calls three external subroutines. A **run** records their outputs, each with the guarantee the paper states for it:
--
--   1. **Step 1** (pp.7–9, (10), (12)): a finite set $\bar{\mathcal X}_i=\{x^1,\dots,x^s\}\subseteq\mathbb X$ containing the generators $V$ of $\mathbb X$ (this is (12)), such that $P^{In}_i=\operatorname{conv}\{g_i(x):x\in\bar{\mathcal X}_i\}+\mathbb R^{m_i}_+$ satisfies
--   $$P_i\subseteq P^{In}_i-\varepsilon_1\{\bar c_i\},\qquad P_i=g_i[\mathbb X]+\mathbb R^{m_i}_+ .$$
--   2. **Step 2** (p.9): finitely many sets $F^1,\dots,F^{k_i}$, each consisting of minimal elements of $P^{In}_i$, whose union contains every minimal element of $P^{In}_i$ (the maximal efficient faces of (13) are such a family).
--   3. **Step 3** (p.10, (15)): finite sets $\hat X^j_i\subseteq\mathbb X$ with
--   $$\operatorname{conv}\hat X^j_i\subseteq\bar X^j_i\subseteq\operatorname{conv}\hat X^j_i+B_{\varepsilon_2},\qquad \bar X^j_i=\{x\in\mathbb X:\exists y\in F^j,\ g_i(x)\le y\}\ \text{(14)}.$$
--
--   The **output** of the run is
--   $$\mathcal X_i=\bigcup_{j=1}^{k_i}(\operatorname{conv}\hat X^j_i+B_{\varepsilon_2})\cap\mathbb X,\qquad \mathcal X=\bigcap_{i=1}^N\mathcal X_i .$$
--
--   **Formalization Note** The subroutines ([14, Algorithms 1–2] with (11)–(12), the face enumeration of [1, 25, 24], and [11, Algorithm 5.1]) belong to other papers, which this paper uses only through these guarantees; existence and termination of the subroutines are not part of the run. The left half of (10), $P^{In}_i\subseteq P_i$, is not listed because it follows from $\bar{\mathcal X}_i\subseteq\mathbb X$ and convexity of $f_i$. $P^{In}_i$, $\bar X^j_i$, $\mathcal X_i$ and $\mathcal X$ are computed from the run, not chosen.
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, §4.1–4.4, Algorithm 4.8, pp.7–11, (10), (12), (13)–(15)

import Mathlib
import Definitions.Def_ApproxNashSet_Model

open scoped Pointwise

namespace ApproxNashSet

/-- **A run of Algorithm 4.8** on the game `(f, X)` with `X = conv V` and approximation levels
`ε₁, ε₂`: the outputs of the three external subroutines, for every player `i`, each with the
guarantee the paper states for it.
Feinstein–Hey–Rudloff, arXiv:2310.04176v4, Algorithm 4.8, pp.10–11, with §4.1–4.3, pp.7–10.

* step 1 (pp.7–9, (10), (12)): a finite set `Xbar i = {x¹, …, xˢ} ⊆ X` containing the generators
  `V` of `X` ((12)), such that `PIn_i := conv{gᵢ(x) | x ∈ Xbar i} + ℝ^{mᵢ}₊` satisfies the right half
  of (10), `Pᵢ ⊆ PIn_i − ε₁{c̄ᵢ}`;
* step 2 (p.9): finitely many sets `F i 0, …, F i (kᵢ − 1)` of minimal elements of `PIn_i` whose
  union contains every minimal element of `PIn_i` (p.9: "the union of all maximal efficient faces of
  (13) equals the set of minimal elements of PIn_i");
* step 3 (p.10, (15)): finite sets `Xhat i j ⊆ X` with
  `conv Xhat i j ⊆ X̄ʲᵢ ⊆ conv Xhat i j + B_{ε₂}`, where `X̄ʲᵢ` is the convex projection (14).

**Formalization Note.** The subroutines ([14, Algorithm 1/2], [1, 25, 24], [11, Algorithm 5.1]) are
external to the paper, which specifies them only by these guarantees. Step 2 asks for any finite
cover of the minimal elements by sets of minimal elements; the maximal efficient faces are one such
cover. The left half of (10), `PIn_i ⊆ Pᵢ`, is not listed: it follows from `Xbar i ⊆ X` and the
convexity of the costs. -/
structure Run {ι : Type} [Fintype ι] (n : ι → ℕ) (f : ι → Joint n → ℝ) (X : Set (Joint n))
    (V : Finset (Joint n)) (ε₁ ε₂ : ℝ) where
  /-- Step 1: the finite point set `X̄` produced by the modified [14, Algorithm 1]. -/
  Xbar : ι → Finset (Joint n)
  /-- (12): the generators of `X` are added to `X̄`. -/
  gen_subset : ∀ i, V ⊆ Xbar i
  /-- `X̄ = {x¹, …, xˢ} ⊆ X` (p.11). -/
  Xbar_subset : ∀ i, (↑(Xbar i) : Set (Joint n)) ⊆ X
  /-- Right half of (10): `Pᵢ ⊆ PIn_i − ε₁{c̄ᵢ}`. -/
  step1 : ∀ i, upperImage (g n f i) X ⊆
    (fun p => p - ε₁ • cbar n i) '' PIn (g n f i) (↑(Xbar i) : Set (Joint n))
  /-- Step 2: the number `kᵢ` of sets. -/
  k : ι → ℕ
  /-- Step 2: the sets `F¹, …, F^{kᵢ}` (the maximal efficient faces of (13)). -/
  F : ∀ i, Fin (k i) → Set (Obj n i)
  /-- Every `Fʲ` consists of minimal elements of `PIn_i`. -/
  F_minimal : ∀ i j, F i j ⊆ MinSet (PIn (g n f i) (↑(Xbar i) : Set (Joint n)))
  /-- The union of the `Fʲ` contains every minimal element of `PIn_i`. -/
  F_cover : ∀ i, MinSet (PIn (g n f i) (↑(Xbar i) : Set (Joint n))) ⊆ ⋃ j, F i j
  /-- Step 3: the finite sets `X̂ʲᵢ`. -/
  Xhat : ∀ i, Fin (k i) → Finset (Joint n)
  /-- `X̂ʲᵢ ⊆ X` (p.10). -/
  Xhat_subset : ∀ i j, (↑(Xhat i j) : Set (Joint n)) ⊆ X
  /-- Left half of (15): `conv X̂ʲᵢ ⊆ X̄ʲᵢ`. -/
  step3_inner : ∀ i j, convexHull ℝ (↑(Xhat i j) : Set (Joint n)) ⊆ convProj (g n f i) X (F i j)
  /-- Right half of (15): `X̄ʲᵢ ⊆ conv X̂ʲᵢ + B_{ε₂}`. -/
  step3_outer : ∀ i j, convProj (g n f i) X (F i j) ⊆
    convexHull ℝ (↑(Xhat i j) : Set (Joint n)) + ballL1 n ε₂

/-- **The per-player output** `𝒳ᵢ = ⋃_{j=1}^{kᵢ} (conv X̂ʲᵢ + B_{ε₂}) ∩ X` of a run.
arXiv:2310.04176v4, Algorithm 4.8, step 3, p.11 (and p.10). -/
def Run.calXi {ι : Type} [Fintype ι] {n : ι → ℕ} {f : ι → Joint n → ℝ} {X : Set (Joint n)}
    {V : Finset (Joint n)} {ε₁ ε₂ : ℝ} (R : Run n f X V ε₁ ε₂) (i : ι) : Set (Joint n) :=
  (⋃ j, (convexHull ℝ (↑(R.Xhat i j) : Set (Joint n)) + ballL1 n ε₂)) ∩ X

/-- **The output** `𝒳 = ⋂_{i=1}^N 𝒳ᵢ` of a run of Algorithm 4.8.
arXiv:2310.04176v4, Algorithm 4.8, "Output", p.11. -/
def Run.calX {ι : Type} [Fintype ι] {n : ι → ℕ} {f : ι → Joint n → ℝ} {X : Set (Joint n)}
    {V : Finset (Joint n)} {ε₁ ε₂ : ℝ} (R : Run n f X V ε₁ ε₂) : Set (Joint n) :=
  ⋂ i, R.calXi i

end ApproxNashSet



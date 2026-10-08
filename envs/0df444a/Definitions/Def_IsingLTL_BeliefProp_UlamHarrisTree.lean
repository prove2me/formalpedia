-- Prove2me | Definitions.Def_IsingLTL_BeliefProp_UlamHarrisTree
-- name    : IsingLTL_BeliefProp_UlamHarrisTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:37.747468+00:00
-- url     : https://prove2.me/theorems/733d7d49-5677-42ac-bd11-d1437958317b
-- title:
--   Rooted trees in Ulam–Harris form, $\mathsf T(k)$, $\partial\mathsf T(k)$, and the Ising models $\mu^{\ell,0}$, $\mu^{\ell,+}$ on $\mathsf T(\ell)$
-- statement:
--   A locally finite rooted tree is encoded by its **offspring function** $\omega:\mathbb N^{<\mathbb N}\to\mathbb N$ on finite words of natural numbers. The root is the empty word $\varnothing$; the vertices of generation $k$ are the words $[i_1,\dots,i_k]$ with $i_{m+1}<\omega([i_1,\dots,i_m])$ for every $m<k$; the children of a vertex $w$ are $w\,i$ for $i<\omega(w)$, so $\Delta_w=\omega(w)$ is the offspring number of $w$. Then:
--
--   1. $\partial\mathsf T(k)$ is the set of vertices of generation $k$;
--   2. $\mathsf T(k)$ is the set of vertices of generations $0,\dots,k$, with the parent–child edges;
--   3. for a vertex $i$, $\mathsf T_i$ (in $\mathsf T(r)$) is the subtree of $i$ and all its descendants in $\mathsf T(r)$.
--
--   For a field $\underline B=\{B_w\}$ indexed by words and $\beta\in\mathbb R$, the Ising models on $\mathsf T(\ell)$ with **free** and **plus boundary conditions** are
--   $$\mu^{\ell,0}(\underline x)=\frac1{Z^{\ell,0}}\exp\Big\{\beta\sum_{(ij)\in\mathsf T(\ell)}x_ix_j+\sum_{i\in\mathsf T(\ell)}B_ix_i\Big\},$$
--   $$\mu^{\ell,+}(\underline x)=\frac1{Z^{\ell,+}}\exp\Big\{\beta\sum_{(ij)\in\mathsf T(\ell)}x_ix_j+\sum_{i\in\mathsf T(\ell)}B_ix_i\Big\}\,\mathbb I\big(\underline x_{\partial\mathsf T(\ell)}=(+)_{\partial\mathsf T(\ell)}\big),$$
--   and $m^{\ell,+/0}(\underline B)=\langle\mu^{\ell,+/0},x_\varnothing\rangle$ are the corresponding **root magnetizations**.
--
--   These objects carry every statement about Ising models on trees in §4 of the paper.
--
--   **Formalization Note** The field $\underline B$ is a nonrandom function of the vertex (word); the paper does not say whether the field may depend on the tree. Values of $\omega$ and $\underline B$ at words that are not vertices are never used.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, §2.1, pp. 3–4 (T(t), ∂T(k)); p. 10, eqs. (4.1)–(4.2); p. 12 (root magnetizations m^{ℓ,+/0}); p. 14 (subtree T_i)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_IsingModel

namespace IsingLTL.BeliefProp

/-- Generation `k` of the rooted tree with offspring function `ω` in Ulam–Harris form: the words
`[i₁, …, i_k]` with `i_{m+1} < ω [i₁, …, i_m]` for every `m < k`. Generation `0` is the root
`ø = []`, and `ω w` is the offspring number `Δ_w` of the vertex `w`. This is `∂T(k)`
(Dembo–Montanari, arXiv:0804.4726v3, §2.1 pp. 3–4 and Definition 2.5, p. 6). -/
def gen (ω : List ℕ → ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | k + 1 => (gen ω k).biUnion (fun w => (Finset.range (ω w)).image (fun i => w ++ [i]))

/-- The vertices `T(k)` of the first `k` generations of the tree with offspring function `ω`
(arXiv:0804.4726v3, p. 4): the words of length `≤ k` of `gen ω 0, …, gen ω k`. -/
def ballTree (ω : List ℕ → ℕ) (k : ℕ) : Finset (List ℕ) :=
  (Finset.range (k + 1)).biUnion (gen ω)

/-- The vertices of the subtree `T_i` of the vertex `i` and all its descendants in `T(r)`
(arXiv:0804.4726v3, Lemma 4.4, p. 14): the words of `T(r)` that have `i` as a prefix. -/
def subtreeAt (ω : List ℕ → ℕ) (r : ℕ) (i : List ℕ) : Finset (List ℕ) :=
  (ballTree ω r).filter (fun w => i <+: w)

/-- The parent–child graph on words: `v` and `w` are adjacent when one is obtained from the other
by appending one letter. The tree `T(k)` is the subgraph induced on `ballTree ω k`; its edges
are exactly the pairs `(w, w ++ [i])` with `i < ω w`. -/
def treeGraph : SimpleGraph (List ℕ) :=
  SimpleGraph.fromRel (fun v w => w ≠ [] ∧ w.dropLast = v)

instance : DecidableRel treeGraph.Adj := fun a b =>
  decidable_of_iff' _ (SimpleGraph.fromRel_adj _ a b)

/-- The Ising models on `T(ℓ)` with free (`plus = false`, (4.1)) and plus (`plus = true`, (4.2))
boundary conditions (arXiv:0804.4726v3, p. 10): `μ^{ℓ,0}` and `μ^{ℓ,+}`, the latter pinning every
vertex of `∂T(ℓ)` to `+1` (field `B_i = +∞`).

Formalization Note: the field `B : List ℕ → ℝ` is a nonrandom function of the vertex (word);
the paper does not say whether the field may depend on the tree. -/
noncomputable def isingTree (ω : List ℕ → ℕ) (β : ℝ) (B : List ℕ → ℝ) (ℓ : ℕ) (plus : Bool) :
    ({w // w ∈ ballTree ω ℓ} → Bool) → ℝ :=
  isingOn treeGraph β B (if plus then gen ω ℓ else ∅) (ballTree ω ℓ)

/-- The root magnetizations `m^{ℓ,+}(B) = ⟨μ^{ℓ,+}, x_ø⟩` (`plus = true`) and
`m^{ℓ,0}(B) = ⟨μ^{ℓ,0}, x_ø⟩` (`plus = false`) (arXiv:0804.4726v3, Lemma 4.3, p. 12). -/
noncomputable def rootMag (ω : List ℕ → ℕ) (β : ℝ) (B : List ℕ → ℝ) (ℓ : ℕ) (plus : Bool) : ℝ :=
  magOn (ballTree ω ℓ) (isingTree ω β B ℓ plus) []

end IsingLTL.BeliefProp



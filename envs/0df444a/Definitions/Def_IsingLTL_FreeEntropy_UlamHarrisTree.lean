-- Prove2me | Definitions.Def_IsingLTL_FreeEntropy_UlamHarrisTree
-- name    : IsingLTL_FreeEntropy_UlamHarrisTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:17.092333+00:00
-- url     : https://prove2.me/theorems/a7eb1a52-82ea-46d8-9628-4dc06e091397
-- title:
--   Rooted trees by offspring functions: generations $\partial T(k)$, $T(k)$, subtrees, and the Ising models $\mu^{\ell,0}$, $\mu^{\ell,+}$ ((4.1)-(4.2))
-- statement:
--   A locally finite rooted tree is described by its **offspring function** $\omega$, which assigns to every finite word $w=(i_1,\dots,i_k)$ of natural numbers its number of offspring $\Delta_w=\omega(w)$. The vertices of the tree are the words with $i_{m+1}<\omega(i_1,\dots,i_m)$ for every $m$; the root $\varnothing$ is the empty word, and the children of $w$ are $w\,i$ for $i<\omega(w)$ (the edges of the tree join $w$ and $w\,i$). Generation $k$, written $\partial T(k)$, is the set of vertices of length $k$, and $T(k)$ is the subtree of the first $k$ generations (vertices of length at most $k$). For a vertex $i$ of $T(r)$, $T_i$ is the subtree of $i$ and its descendants in $T(r)$.
--
--   For $\ell\ge1$, the Ising models on $T(\ell)$ with **free** and **plus** boundary conditions are
--   $$\mu^{\ell,0}(\underline x)=\frac{1}{Z^{\ell,0}}\exp\Big\{\beta\sum_{(ij)\in T(\ell)}x_ix_j+\sum_{i\in T(\ell)}B_ix_i\Big\},\qquad \mu^{\ell,+}(\underline x)=\frac{1}{Z^{\ell,+}}\exp\Big\{\beta\sum_{(ij)\in T(\ell)}x_ix_j+\sum_{i\in T(\ell)}B_ix_i\Big\}\,\mathbb I\big(\underline x_{\partial T(\ell)}=(+)_{\partial T(\ell)}\big),$$
--   and $m^{\ell,+/0}(\underline B)=\langle\mu^{\ell,+/0},x_\varnothing\rangle$ are the **root magnetizations**.
--
--   These objects carry the analysis of Ising models on trees in Section 4.
--
--   **Formalization Note** This is the Ulam–Harris encoding: every finite rooted tree is, up to root-preserving isomorphism, the tree $T(k)$ of some offspring function. The field $B$ is a nonrandom function of the vertex (word); the paper does not say whether the field may depend on the tree.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, pp. 3-4 (§2.1); p. 6, Definition 2.5; p. 10, (4.1)-(4.2); p. 12, Lemma 4.3; p. 14, Lemma 4.4

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_IsingModel

namespace IsingLTL.FreeEntropy

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

end IsingLTL.FreeEntropy



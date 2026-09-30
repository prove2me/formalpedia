-- Prove2me | Definitions.Def_XuMannorRobust_Lasso_IsRobustOn
-- name    : XuMannorRobust_Lasso_IsRobustOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:21:41.466295+00:00
-- url     : https://prove2.me/theorems/ad090a23-1b3b-48f5-b7a2-52d02e13de56
-- title:
--   $(K, \epsilon(\cdot))$-robustness of a learning algorithm on a sample set $\mathcal Z$
-- statement:
--   Let $\mathcal Z$ be a set of samples (a subset of some ambient space), $\mathcal H$ a set of hypotheses, $l : \mathcal H \times \mathcal Z \to \mathbb R$ a loss function, and $\mathcal A : \mathcal Z^n \to \mathcal H$ a learning algorithm, which maps a training set $\mathbf s = (s_1, \dots, s_n)$ to a hypothesis $\mathcal A_{\mathbf s}$. For $K \in \mathbb N$ and $\epsilon(\cdot) : \mathcal Z^n \to \mathbb R$, the algorithm $\mathcal A$ is **$(K, \epsilon(\cdot))$-robust** if $\mathcal Z$ can be partitioned into $K$ disjoint sets $C_1, \dots, C_K$ such that for every training set $\mathbf s \in \mathcal Z^n$,
--
--   $$\forall s \in \mathbf s,\ \forall z \in \mathcal Z,\ \forall i = 1, \dots, K:\quad s, z \in C_i \implies |l(\mathcal A_{\mathbf s}, s) - l(\mathcal A_{\mathbf s}, z)| \le \epsilon(\mathbf s).$$
--
--   The partition is fixed once for the algorithm; it does not depend on the training set. Robustness says that a test sample falling in the same cell as some training sample incurs nearly the same loss as that training sample.
--
--   **Formalization Note** The sample space is a set `Z` inside an ambient type `α`; the cells are subsets of `Z`, pairwise disjoint, and their union contains `Z` (so they partition it; empty cells are allowed). Training sets are maps `Fin n → α` whose points all lie in `Z`, and $\epsilon$ is defined on all such maps. The existential over the partition precedes the universal over training sets. No measurability is required: the property is purely combinatorial.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 396, Definition 2

import Mathlib

namespace XuMannorRobust.Lasso

/-- **(K, ε(·))-robustness on a sample set** (Xu & Mannor 2012, p. 396, Definition 2), for a sample
space `Z` given as a subset of an ambient type `α`. The algorithm `A : Zⁿ → H` is `(K, ε(·))`-robust
for the loss `l` if `Z` can be partitioned into `K` disjoint sets `C_1, …, C_K`, fixed once and for
all, such that for every training set `s ∈ Zⁿ`, every training point `s_j`, every `z ∈ Z` and every
cell `C_i`: if `s_j, z ∈ C_i` then `|l(A_s, s_j) − l(A_s, z)| ≤ ε(s)`.

The partition is chosen before the training set (`∃ C` precedes `∀ s`). The cells lie inside `Z`,
are pairwise disjoint and cover `Z`; empty cells are allowed. No measurability is required: this
notion is purely combinatorial. -/
def IsRobustOn {α H : Type*} {n : ℕ} (Z : Set α) (l : H → α → ℝ)
    (A : (Fin n → α) → H) (K : ℕ) (ε : (Fin n → α) → ℝ) : Prop :=
  ∃ C : Fin K → Set α,
    (∀ i, C i ⊆ Z) ∧
    Z ⊆ ⋃ i, C i ∧
    Pairwise (Function.onFun Disjoint C) ∧
    ∀ s : Fin n → α, (∀ j, s j ∈ Z) →
      ∀ j : Fin n, ∀ z ∈ Z, ∀ i : Fin K,
        s j ∈ C i → z ∈ C i → |l (A s) (s j) - l (A s) z| ≤ ε s

end XuMannorRobust.Lasso



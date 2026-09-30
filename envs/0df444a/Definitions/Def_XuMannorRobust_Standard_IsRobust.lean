-- Prove2me | Definitions.Def_XuMannorRobust_Standard_IsRobust
-- name    : XuMannorRobust_Standard_IsRobust
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T15:30:17.542688+00:00
-- url     : https://prove2.me/theorems/80a5c48e-25b8-4f69-bcad-a4d7970fe9e0
-- title:
--   $(K, \epsilon(\cdot))$-robust learning algorithm (Definition 2)
-- statement:
--   Let $\mathcal Z$ be a measurable space, $\mathcal H$ a set of hypotheses, $l : \mathcal H \times \mathcal Z \to \mathbb R$ a loss, and $\mathcal A : \mathcal Z^n \to \mathcal H$ a learning algorithm; write $\mathcal A_{\mathbf s}$ for the hypothesis learned from the training set $\mathbf s = (s_1,\dots,s_n)$. For $K \in \mathbb N$ and $\epsilon(\cdot) : \mathcal Z^n \to \mathbb R$, the algorithm $\mathcal A$ is **$(K, \epsilon(\cdot))$-robust** if $\mathcal Z$ can be partitioned into $K$ disjoint measurable sets $C_1, \dots, C_K$ such that, for every training set $\mathbf s \in \mathcal Z^n$,
--
--   $$\forall s \in \mathbf s,\ \forall z \in \mathcal Z,\ \forall i = 1, \dots, K:\quad s, z \in C_i \implies |l(\mathcal A_{\mathbf s}, s) - l(\mathcal A_{\mathbf s}, z)| \le \epsilon(\mathbf s).$$
--
--   The partition is fixed before the training set is seen: one partition serves every $\mathbf s$, and only the tolerance $\epsilon(\mathbf s)$ may depend on $\mathbf s$. A test point landing in the same cell as a training point incurs a loss close to that training point's loss.
--
--   **Formalization Note** The cells are required to be measurable sets, which the paper omits ("we ignore the issue of measurability"); it is needed for $\mu(C_i)$ to be meaningful. Empty cells are allowed, as in the paper. The partition is a family `C : Fin K → Set Z` that is pairwise disjoint with union $\mathcal Z$, and the existential over `C` precedes the universal over training sets.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 396, Definition 2, Eq. (2)

import Mathlib

namespace XuMannorRobust.Standard

/-- **(K, ε(·))-robustness** (Xu & Mannor 2012, p. 396, Definition 2). The algorithm
`A : Zⁿ → H` is `(K, ε(·))`-robust for the loss `l` if `Z` can be partitioned into `K` disjoint
(measurable) sets `C_1, …, C_K`, fixed once and for all, such that for every training set `s`,
every training point `s_j`, every `z ∈ Z` and every cell `C_i`: if `s_j, z ∈ C_i` then
`|l(A_s, s_j) − l(A_s, z)| ≤ ε(s)`.

The partition is chosen before the training set (`∃ C` precedes `∀ s`). Measurability of the cells
is added to the paper's definition, which ignores measurability. Empty cells are allowed. -/
def IsRobust {Z H : Type*} [MeasurableSpace Z] {n : ℕ} (l : H → Z → ℝ)
    (A : (Fin n → Z) → H) (K : ℕ) (ε : (Fin n → Z) → ℝ) : Prop :=
  ∃ C : Fin K → Set Z,
    (∀ i, MeasurableSet (C i)) ∧
    Pairwise (Function.onFun Disjoint C) ∧
    (⋃ i, C i) = Set.univ ∧
    ∀ s : Fin n → Z, ∀ j : Fin n, ∀ z : Z, ∀ i : Fin K,
      s j ∈ C i → z ∈ C i → |l (A s) (s j) - l (A s) z| ≤ ε s

end XuMannorRobust.Standard



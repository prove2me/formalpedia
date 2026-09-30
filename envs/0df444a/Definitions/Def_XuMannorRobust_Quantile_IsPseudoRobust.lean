-- Prove2me | Definitions.Def_XuMannorRobust_Quantile_IsPseudoRobust
-- name    : XuMannorRobust_Quantile_IsPseudoRobust
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T16:09:01.967321+00:00
-- url     : https://prove2.me/theorems/9086dc05-a1c1-474f-8881-11cc94e54dd4
-- title:
--   $(K, \epsilon(\cdot), \hat n(\cdot))$ pseudo robust learning algorithm (Definition 5)
-- statement:
--   Let $\mathcal Z$ be a measurable space, $\mathcal H$ a set of hypotheses, $l : \mathcal H \times \mathcal Z \to \mathbb R$ a loss and $\mathcal A : \mathcal Z^n \to \mathcal H$ a learning algorithm, with $\mathcal A_{\mathbf s}$ the hypothesis learned from $\mathbf s = (s_1, \dots, s_n)$. For $K \in \mathbb N$, $\epsilon(\cdot) : \mathcal Z^n \to \mathbb R$ and $\hat n(\cdot) : \mathcal Z^n \to \{1, \dots, n\}$, the algorithm is **$(K, \epsilon(\cdot), \hat n(\cdot))$ pseudo robust** if $\mathcal Z$ can be partitioned into $K$ disjoint measurable sets $C_1, \dots, C_K$ such that for every $\mathbf s \in \mathcal Z^n$ there is a subset $\hat{\mathbf s}$ of the training samples with $|\hat{\mathbf s}| = \hat n(\mathbf s)$ satisfying
--
--   $$\forall s \in \hat{\mathbf s},\ \forall z \in \mathcal Z,\ \forall i = 1, \dots, K:\quad s, z \in C_i \implies |l(\mathcal A_{\mathbf s}, s) - l(\mathcal A_{\mathbf s}, z)| \le \epsilon(\mathbf s).$$
--
--   The partition is fixed before the training set is seen; only the good subset $\hat{\mathbf s}$ and the tolerance $\epsilon(\mathbf s)$ depend on $\mathbf s$. With $\hat n \equiv n$ this is $(K, \epsilon(\cdot))$-robustness.
--
--   **Formalization Note** The subset $\hat{\mathbf s}$ is a set of indices $S \subseteq \{0, \dots, n-1\}$ with $|S| = \hat n(\mathbf s)$, so repeated sample values are counted separately. The codomain $\{1, \dots, n\}$ of $\hat n$ is the first conjunct of the definition. Measurability of the cells is added (the paper ignores measurability); it is needed for $\mu(C_i)$. Empty cells are allowed.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 401, Definition 5

import Mathlib

namespace XuMannorRobust.Quantile

/-- **(K, ε(·), n̂(·)) pseudo robustness** (Xu & Mannor 2012, p. 401, Definition 5). The algorithm
`A : Zⁿ → H` is `(K, ε(·), n̂(·))` pseudo robust for the loss `l`, where `n̂(·)` takes values in
`{1, …, n}`, if `Z` can be partitioned into `K` disjoint (measurable) sets `C_1, …, C_K`, fixed once
and for all, such that for every training set `s` there is a set `ŝ` of `n̂(s)` training samples
(encoded as a set of indices `S ⊆ {0, …, n-1}` with `|S| = n̂(s)`) with: for every `j ∈ S`, every
`z ∈ Z` and every cell `C_i`, if `s_j, z ∈ C_i` then `|l(A_s, s_j) − l(A_s, z)| ≤ ε(s)`.

The partition precedes the training set (`∃ C` before `∀ s`); `ŝ` may depend on `s`. The codomain
`{1, …, n}` of `n̂` is the first conjunct. Measurability of the cells is added to the paper's
definition, which ignores measurability. Empty cells are allowed. -/
def IsPseudoRobust {Z H : Type*} [MeasurableSpace Z] {n : ℕ} (l : H → Z → ℝ)
    (A : (Fin n → Z) → H) (K : ℕ) (ε : (Fin n → Z) → ℝ) (nhat : (Fin n → Z) → ℕ) : Prop :=
  (∀ s : Fin n → Z, 1 ≤ nhat s ∧ nhat s ≤ n) ∧
  ∃ C : Fin K → Set Z,
    (∀ i, MeasurableSet (C i)) ∧
    Pairwise (Function.onFun Disjoint C) ∧
    (⋃ i, C i) = Set.univ ∧
    ∀ s : Fin n → Z, ∃ S : Finset (Fin n), S.card = nhat s ∧
      ∀ j ∈ S, ∀ z : Z, ∀ i : Fin K,
        s j ∈ C i → z ∈ C i → |l (A s) (s j) - l (A s) z| ≤ ε s

end XuMannorRobust.Quantile



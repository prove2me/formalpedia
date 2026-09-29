-- Prove2me | Definitions.Def_VapnikChervonenkis_Shared_growthFunction
-- name    : VapnikChervonenkis_Shared_growthFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:33:46.842752+00:00
-- url     : https://prove2.me/theorems/df8027eb-9571-4b1e-a4f5-11c82e70515e
-- title:
--   The growth function m^S(r)
-- statement:
--   Let $X$ be a set and $S$ a collection of subsets of $X$. A **sample** of size $r$ is a finite sequence $x_1, \dots, x_r$ of elements of $X$; repetitions are allowed. Each set $A \in S$ **induces** in the sample the subsample consisting of those terms $x_i$ that belong to $A$.
--
--   The **index** of $S$ with respect to the sample, $\Delta^S(x_1, \dots, x_r)$, is the number of different subsamples induced by the sets of $S$. A subsample is determined by the positions it keeps, so
--
--   $$
--   \Delta^S(x_1, \dots, x_r) = \#\bigl\{\, \{ i : x_i \in A \} \;:\; A \in S \,\bigr\} ,
--   $$
--
--   the number of distinct subsets of $\{1, \dots, r\}$ of the form $\{i : x_i \in A\}$ with $A \in S$. In particular $\Delta^S(x_1, \dots, x_r) \le 2^r$.
--
--   The **growth function** of $S$ is
--
--   $$
--   m^S(r) = \max_{x_1, \dots, x_r \in X} \Delta^S(x_1, \dots, x_r),
--   $$
--
--   the maximum over all samples of size $r$. For instance, for the rays $\{y \le a\}$ on the real line $m^S(r) = r + 1$, and for the open subsets of $[0,1]$ $m^S(r) = 2^r$.
--
--   The growth function measures how rich the class $S$ is on finite samples. It is the quantity through which Vapnik and Chervonenkis bound the uniform deviation of relative frequencies from probabilities.
--
--   **Shared definition.** This one definition serves two missions of the paper: *01-growth-function* (Theorem 1, p. 267, and the index bound of p. 268) and *02-vc-inequality* (the semi-sample bound, p. 271; Theorem 2 and its corollary, p. 269; Theorem 3, p. 271). The index $\Delta^S$ is the shared definition `VapnikChervonenkis.Shared.index`.
--
--   **Formalization Note.** A sample of size $r$ is a function `x : Fin r → X` (positions $0, \dots, r-1$ instead of $1, \dots, r$), and the subsample induced by $A$ is the set of positions `{i | x i ∈ A} : Finset (Fin r)`. Counting position sets, not point sets, is the paper's sequence model: two positions carrying the same point are never separated. `index S x` is the number of such position sets, and `growthFunction S r` is the supremum in $\mathbb{N}$ of `index S x` over all `x : Fin r → X`. The family is bounded by $2^r$, so the supremum is a maximum whenever a sample exists. When $X$ is empty and $r \ge 1$ there are no samples and the value is $0$. The empty sample has index $1$ when $S$ is nonempty and $0$ when $S = \emptyset$, so $m^S(0) = 1$ exactly when $S$ is nonempty.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 265, Subsection 1 (Subsidiary definitions)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index

namespace VapnikChervonenkis.Shared

/-- The **growth function** `m^S(r) = max Δ^S(x_1, …, x_r)`, the maximum being taken over all
samples of size `r` (Vapnik and Chervonenkis 1971, p. 265, Subsection 1). The family of indices is
bounded by `2 ^ r`, so this supremum in `ℕ` is a genuine maximum whenever `X` is nonempty or
`r = 0`; for `X` empty and `r ≥ 1` there are no samples and the value is `0`. -/
noncomputable def growthFunction {X : Type*} (S : Set (Set X)) (r : ℕ) : ℕ :=
  ⨆ x : Fin r → X, index S x

end VapnikChervonenkis.Shared



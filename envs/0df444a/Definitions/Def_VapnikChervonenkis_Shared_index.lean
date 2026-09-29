-- Prove2me | Definitions.Def_VapnikChervonenkis_Shared_index
-- name    : VapnikChervonenkis_Shared_index
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:33:08.214731+00:00
-- url     : https://prove2.me/theorems/d6a49bf5-a157-4f29-824e-6568cc8ba3fd
-- title:
--   The index Δ^S(x_1, …, x_r) of a class of events on a sample
-- statement:
--   Let $X$ be a set and $S$ a collection of subsets of $X$. A **sample** of size $r$ is a finite sequence $x_1, \dots, x_r$ of elements of $X$; repetitions are allowed. Each set $A \in S$ **induces** in the sample the subsample consisting of those terms $x_i$ that belong to $A$.
--
--   The **index** of $S$ with respect to the sample, $\Delta^S(x_1, \dots, x_r)$, is the number of different subsamples induced by the sets of $S$. A subsample is determined by the positions it keeps, so
--
--   $$
--   \Delta^S(x_1, \dots, x_r) = \#\bigl\{\, \{ i : x_i \in A \} \;:\; A \in S \,\bigr\} ,
--   $$
--
--   the number of distinct subsets of $\{1, \dots, r\}$ of the form $\{i : x_i \in A\}$ with $A \in S$. In particular $0 \le \Delta^S(x_1, \dots, x_r) \le 2^r$, and $\Delta^S = 0$ only when $S$ is empty.
--
--   The index measures how many ways the class $S$ can split a given sample. Its maximum over samples is the growth function $m^S(r)$ (Theorems 1–3), and its binary logarithm, averaged over random samples, is the entropy $H^S(l)$ that characterizes uniform convergence of relative frequencies (Theorem 4).
--
--   **Shared definition.** This one definition serves all three missions of the paper: *01-growth-function* ($\Delta^S \le 2^r$, p. 265; Lemma 1, p. 266; the index bound of p. 268), *02-vc-inequality* (the permutation bound, p. 271, and through the growth function Theorems 2 and 3, pp. 269–271) and *03-entropy-criterion* (inequality (12), p. 272; the entropy and Lemmas 3–4, p. 273; Theorem 4 and its proof, pp. 275–280).
--
--   **Formalization Note.** A sample of size $r$ is a function `x : Fin r → X` (positions $0, \dots, r-1$ instead of $1, \dots, r$), and the subsample induced by $A$ is the set of positions `{i | x i ∈ A} : Finset (Fin r)`. Counting position sets, not point sets, is the paper's sequence model: two positions carrying the same point are never separated.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 265, Subsection 1 (Subsidiary definitions)

import Mathlib

namespace VapnikChervonenkis.Shared

open Classical in
/-- The **index** `Δ^S(x_1, …, x_r)` of a class `S` of subsets of `X` with respect to a sample
`x = (x_0, …, x_{r-1})` (Vapnik and Chervonenkis 1971, p. 265, Subsection 1): the number of
different subsamples induced in the sample by the sets of `S`. The sample is a sequence
`x : Fin r → X` (repetitions allowed), and the subsample induced by `A` is recorded as the set of
positions `{i | x i ∈ A} : Finset (Fin r)`; `index S x` counts the distinct position sets arising
from some `A ∈ S`. -/
noncomputable def index {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) : ℕ :=
  (Finset.univ.filter (fun t : Finset (Fin r) => ∃ A ∈ S, ∀ i, i ∈ t ↔ x i ∈ A)).card

end VapnikChervonenkis.Shared



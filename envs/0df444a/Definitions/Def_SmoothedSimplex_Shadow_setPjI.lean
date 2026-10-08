-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_setPjI
-- name    : SmoothedSimplex_Shadow_setPjI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:05:16.861706+00:00
-- url     : https://prove2.me/theorems/c2848d9c-5e38-4947-b8d6-7deffd316ebe
-- title:
--   Definition 4.0.8 — the set $P^j_I$
-- statement:
--   For $I\in\binom{[n]}{d}$ and $j\in I$, $P^j_I$ is the set of tuples $(a_1,\dots,a_n)$ of vectors in $\mathbb R^d$ satisfying
--
--   1. for every unit vector $q$, if $\mathrm{optSimp}_q(a_1,\dots,a_n)\neq\emptyset$, then $s\le 2$, where $s$ is the real number for which $sq\in\triangle(\mathrm{optSimp}_q(a_1,\dots,a_n))$;
--   2. $\mathrm{dist}(a_i,a_k)\le 4$ for $i,k\in I-\{j\}$;
--   3. $\mathrm{dist}(a_j,\mathrm{Aff}(A_{I-\{j\}}))\le 4$; and
--   4. $\mathrm{dist}(a_j^{\perp},a_i)\le 4$ for all $i\in I-\{j\}$, where $a_j^{\perp}$ is the orthogonal projection of $a_j$ onto $\mathrm{Aff}(A_{I-\{j\}})$.
--
--   Every tuple in $P$ lies in $P^j_I$ (Proposition 4.0.9); $P^j_I$ keeps only the geometric consequences of $P$ that survive the change of variables used to prove Lemma 4.0.11.
--
--   **Formalization Note** The page calls $P^j_I$ "the set of $a_1,\dots,a_d$", but condition 1 involves all of $a_1,\dots,a_n$, so it is a set of $n$-tuples. In condition 1, $q$ ranges over unit vectors ($s$ is the norm of $sq$ in the proof of Proposition 4.0.9), and the condition is required for every element of $\mathrm{optSimp}_q$ when there are several. $\mathrm{dist}(x,\mathrm{Aff}(S))$ is the infimum distance to the affine span, and $a_j^\perp$ is the point $p$ of the affine span with $a_j-p$ orthogonal to its direction. Indices are 0-based.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Definition 4.0.8, printed p. 41 (PDF p. 41)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_optSimp

namespace SmoothedSimplex.Shadow

open scoped RealInnerProductSpace

/-- The set `P^j_I` (Spielman & Teng, arXiv:cs/0111050v7, Definition 4.0.8, printed p. 41,
PDF p. 41). For `I ∈ ([n] choose d)` and `j ∈ I`, `P^j_I` is the set of `a₁, …, aₙ` satisfying
1. for all `q`, if `optSimp_q(a₁, …, aₙ) ≠ ∅`, then `s ≤ 2`, where `s` is the real number for
   which `sq ∈ △(optSimp_q(a₁, …, aₙ))`;
2. `dist(aᵢ, a_k) ≤ 4` for `i, k ∈ I − {j}`;
3. `dist(a_j, Aff(A_{I−{j}})) ≤ 4`;
4. `dist(a_j^⊥, aᵢ) ≤ 4` for all `i ∈ I − {j}`, where `a_j^⊥` is the orthogonal projection of
   `a_j` onto `Aff(A_{I−{j}})`.

**Formalization Note.**
* The page says "the set of `a₁, …, a_d`", but condition (1) reads all of `a₁, …, aₙ`: it is a
  set of `n`-tuples.
* In (1), `q` ranges over unit vectors: `s` is the norm of `sq` (proof of Proposition 4.0.9,
  p. 41), and for non-unit `q` the condition would depend on the length of `q`. When
  `optSimp_q` has several elements (probability zero) the condition is required for each.
* `dist(x, Aff(S))` is `Metric.infDist x (affineSpan ℝ S)`. The orthogonal projection `a_j^⊥` is
  the point `p ∈ Aff(A_{I−{j}})` with `a_j − p` orthogonal to the direction of the affine span
  (it exists and is unique since the span is a nonempty finite-dimensional affine subspace).
* `I` and `j` are arbitrary here; the paper uses `|I| = d` and `j ∈ I`. -/
def setPjI {d n : ℕ} (I : Finset (Fin n)) (j : Fin n) :
    Set (Fin n → EuclideanSpace ℝ (Fin d)) :=
  {a | (∀ q : EuclideanSpace ℝ (Fin d), ‖q‖ = 1 → ∀ J ∈ optSimp q a, ∀ s : ℝ,
          s • q ∈ convexHull ℝ (a '' (J : Set (Fin n))) → s ≤ 2) ∧
       (∀ i ∈ I.erase j, ∀ k ∈ I.erase j, dist (a i) (a k) ≤ 4) ∧
       Metric.infDist (a j)
          (affineSpan ℝ (a '' ((I.erase j : Finset (Fin n)) : Set (Fin n))) : Set _) ≤ 4 ∧
       ∃ p ∈ affineSpan ℝ (a '' ((I.erase j : Finset (Fin n)) : Set (Fin n))),
          (∀ v ∈ (affineSpan ℝ (a '' ((I.erase j : Finset (Fin n)) : Set (Fin n)))).direction,
              ⟪a j - p, v⟫ = 0) ∧
          ∀ i ∈ I.erase j, dist p (a i) ≤ 4}

end SmoothedSimplex.Shadow



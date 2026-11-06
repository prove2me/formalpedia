-- Prove2me | Definitions.Def_PolymatroidCover_IsMinimalMinimizer
-- name    : PolymatroidCover_IsMinimalMinimizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:26.305698+00:00
-- url     : https://prove2.me/theorems/48b3787f-6b90-4e89-82de-a9735860f0f8
-- title:
--   Inclusion-wise minimal minimizer of $\min_{X\subseteq D} g(X)$
-- statement:
--   Let $g$ be an integer-valued set function and $D$ a finite set. A set $R$ is an **(inclusion-wise) minimal minimizer** of $\min_{X \subseteq D} g(X)$ if
--
--   1. $R \subseteq D$;
--   2. $g(R) \le g(X)$ for every $X \subseteq D$;
--   3. no proper subset of $R$ is also a minimizer: if $X \subseteq R$ and $g(X) = g(R)$ then $X = R$.
--
--   For a submodular $g$ the minimal minimizer is unique (Lemma 2.3 of the paper, a standard uncrossing fact), which is why the paper speaks of *the* minimal minimizer. The blocking sets of the algorithm are minimal minimizers.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.1, p.12 (PDF p.14), before eq. (8)

import Mathlib

namespace PolymatroidCover

/-- `R` is an (inclusion-wise) minimal minimizer of `min_{X ⊆ D} g(X)` (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.1,
printed p.12 = PDF p.14, the definition of the blocking set before (8)): `R ⊆ D`, `R`
minimizes `g` over the subsets of `D`, and no proper subset of `R` is also a minimizer.

**Formalization Note** For a submodular `g` such an `R` is unique (Lemma 2.3 of the paper,
cited there, not posed here), which is why the paper says "the" minimal minimizer. -/
def IsMinimalMinimizer {n : ℕ} (g : Finset (Fin n) → ℤ) (D R : Finset (Fin n)) : Prop :=
  R ⊆ D ∧ (∀ X ⊆ D, g R ≤ g X) ∧ ∀ X ⊆ R, g X = g R → X = R

end PolymatroidCover



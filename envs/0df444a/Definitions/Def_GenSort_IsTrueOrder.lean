-- Prove2me | Definitions.Def_GenSort_IsTrueOrder
-- name    : GenSort_IsTrueOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:33.641134+00:00
-- url     : https://prove2.me/theorems/2919033e-94f0-48f8-8a1f-41a40aa4e5da
-- title:
--   $\tau^*$: the ordering of $S$ induced by the true permutation
-- statement:
--   An ordering $\tau$ of the sampled multiset $S$ is **induced by the true permutation** $\pi$ if $\tau$ ranks $S_i$ before $S_j$ whenever $S_i \prec_\pi S_j$.
--
--   **Formalization Note** Entries that tie in $\pi$ (repeated samples, or copies of one original vertex) may be ranked either way; every statement quantifies over all such $\tau$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Lemma 3.5, p.8 (PDF p.10)

import Mathlib

namespace GenSort

/-- **`τ*`, the ordering of `S` induced by the true permutation**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Lemma 3.5, p.8 (PDF
p.10): "let `τ*` denote the ordering of vertices in `S` induced by their relative order in the
true permutation `π`". `τ` ranks entry `i` before entry `j` whenever `S_i ≺_π S_j`.

**Formalization Note.** Entries that tie in `π` (repeated samples, or copies of one original
vertex) may be ordered either way; theorems quantify over every such `τ`. -/
def IsTrueOrder {n : ℕ} {R : Type*} {s : ℕ} (r : R → Fin n) (π : Equiv.Perm (Fin n))
    (S : Fin s → R) (τ : Equiv.Perm (Fin s)) : Prop :=
  ∀ i j, π.symm (r (S i)) < π.symm (r (S j)) → τ i < τ j

end GenSort



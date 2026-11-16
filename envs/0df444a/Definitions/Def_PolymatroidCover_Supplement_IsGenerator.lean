-- Prove2me | Definitions.Def_PolymatroidCover_Supplement_IsGenerator
-- name    : PolymatroidCover_Supplement_IsGenerator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:49:46.20273+00:00
-- url     : https://prove2.me/theorems/f7d66148-e0f5-448c-980e-b7a2a1ba66d1
-- title:
--   Generator of a polymatroid: $f(B) = f(E)$
-- statement:
--   Let $f : 2^E \to \mathbb Z_{\ge 0}$ be a polymatroid on a finite ground set $E$. A set $B \subseteq E$ is a **generator** of $f$ if
--
--   $$
--   f(B) = f(E).
--   $$
--
--   For the rank function of a loopless matroid the generators are the spanning sets. A **packing** is a collection of pairwise disjoint generators, and the **packing number** $\kappa(f)$ is the maximum number of pairwise disjoint generators of $f$. Generators are the objects packed in Theorem 1.3.
--
--   **Formalization Note** The ground set is `Fin n` and $f$ is `Finset (Fin n) → ℕ`, as in the mission's published definitions. A generator need not be minimal, and a family of pairwise disjoint generators need not cover $E$.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, p.2 (PDF p.4)

import Mathlib

namespace PolymatroidCover.Supplement

/-- A generator of a polymatroid (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, printed p.2 = PDF p.4):
"A set `B ⊆ E` is a generator if `f(B) = f(E)`."

**Formalization Note** The ground set `E` is `Fin n` and `f : Finset (Fin n) → ℕ`, as in the
published definitions of the mission (`PolymatroidCover.IsPolymatroid`). A generator need not be
minimal; a family of pairwise disjoint generators need not cover `E`. -/
def IsGenerator {n : ℕ} (f : Finset (Fin n) → ℕ) (B : Finset (Fin n)) : Prop :=
  f B = f Finset.univ

end PolymatroidCover.Supplement



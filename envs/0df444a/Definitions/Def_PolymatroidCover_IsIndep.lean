-- Prove2me | Definitions.Def_PolymatroidCover_IsIndep
-- name    : PolymatroidCover_IsIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:23.231532+00:00
-- url     : https://prove2.me/theorems/1dedd682-472f-4116-afa9-23c68abea546
-- title:
--   Independent set of a polymatroid: $f(I) = \sum_{e\in I} f(e)$
-- statement:
--   Let $f$ be a polymatroid on $E$. By submodularity $f(I) \le \sum_{e \in I} f(e)$ for every $I \subseteq E$. A set $I \subseteq E$ is **independent** if equality holds:
--
--   $$
--   f(I) = \sum_{e \in I} f(e).
--   $$
--
--   The independent sets form a downward-closed family $\mathcal I_f$; for the rank function of a loopless matroid they are the usual independent sets, and for a sum of rank functions of $d$ loopless matroids they are the common independent sets. A **covering** of $E$ is a partition of $E$ into independent sets.
--
--   **Formalization Note** The defining condition is the equality, not the inequality (which every set satisfies).
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, p.2 (PDF p.4)

import Mathlib

namespace PolymatroidCover

/-- Independence in a polymatroid (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, printed p.2 = PDF p.4): a set `I ⊆ E`
is independent if `f(I) = ∑_{e ∈ I} f(e)`, where `f(e) := f({e})`.

**Formalization Note** This is an equality, not `≤` (for a polymatroid `f(I) ≤ ∑_{e∈I} f(e)`
always holds by submodularity). Both sides are natural numbers, so no truncation occurs. -/
def IsIndep {n : ℕ} (f : Finset (Fin n) → ℕ) (I : Finset (Fin n)) : Prop :=
  f I = ∑ e ∈ I, f {e}

end PolymatroidCover



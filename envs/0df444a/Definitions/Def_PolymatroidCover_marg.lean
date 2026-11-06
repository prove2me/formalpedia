-- Prove2me | Definitions.Def_PolymatroidCover_marg
-- name    : PolymatroidCover_marg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:23.988877+00:00
-- url     : https://prove2.me/theorems/e0f4ee2a-62a2-4ad8-8023-8aafb900f80b
-- title:
--   Marginal value $f(A \mid T) = f(A\cup T) - f(T)$
-- statement:
--   For a set function $f$ on $E$ and $A, T \subseteq E$, the **marginal value** of $A$ given $T$ is
--
--   $$
--   f(A \mid T) := f(A \cup T) - f(T).
--   $$
--
--   For a single element, $f(e \mid T) := f(T \cup \{e\}) - f(T)$. For a polymatroid, $f(e) - f(e \mid T) \ge 0$ measures how much of the value of $e$ is lost in the presence of $T$; it is the building block of the lower bound $\chi^\circ(f)$ and of the adding condition of the algorithm.
--
--   **Formalization Note** The difference is computed in `ℤ`, so there is no truncated natural subtraction.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, p.2 (PDF p.4) and p.3 (PDF p.5)

import Mathlib

namespace PolymatroidCover

/-- The marginal value `f(A | T) := f(A ∪ T) − f(T)` (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, printed p.2 = PDF p.4);
for a single element this is `f(e | T) := f(T ∪ {e}) − f(T)` (printed p.3 = PDF p.5), i.e.
`marg f {e} T`.

**Formalization Note** Computed in `ℤ` (the values of `f` are cast before subtracting), so
no natural-number truncation occurs. -/
def marg {n : ℕ} (f : Finset (Fin n) → ℕ) (A T : Finset (Fin n)) : ℤ :=
  (f (A ∪ T) : ℤ) - (f T : ℤ)

end PolymatroidCover



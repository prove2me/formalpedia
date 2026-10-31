-- Prove2me | Definitions.Def_KallMayerSLP_KKT_activeSet
-- name    : KallMayerSLP_KKT_activeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:32.934265+00:00
-- url     : https://prove2.me/theorems/c3ef9672-ba57-4da8-a08c-9a9163d80975
-- title:
--   Active set $I(\hat x)$
-- statement:
--   For constraint functions $g_1,\dots,g_m$ and a point $\hat x$, the **active set** is the set of indices of the constraints that hold with equality at $\hat x$:
--   $$
--   I(\hat x):=\{i\mid g_i(\hat x)=0\}.
--   $$
--
--   It appears in the regularity condition RC 0 and in the necessary optimality condition.
--
--   **Formalization Note** Indices are `Fin m`, so $I(\hat x)$ is a `Finset (Fin m)`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, p.62 (PDF 73)

import Mathlib

open Classical

namespace KallMayerSLP.KKT

/-- **The active set `I(x̂)`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3, p.62 (PDF 73):
"`I(x̂) := {i | gᵢ(x̂) = 0}`".

**Formalization Note.** Constraint indices are `Fin m`, so `I(x̂)` is a `Finset (Fin m)`. -/
noncomputable def activeSet {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Finset (Fin m) :=
  {i | g i x = 0}

end KallMayerSLP.KKT



-- Prove2me | Definitions.Def_PolySphereLP_supNorm
-- name    : PolySphereLP_supNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:30.88927+00:00
-- url     : https://prove2.me/theorems/5287f9e5-b0ff-4ec6-9b8b-e25a40f9f973
-- title:
--   Sup norm $\|P\|_\infty$ on the sphere
-- statement:
--   For a real polynomial $P$ on $\mathbb R^n$,
--   $$\|P\|_\infty=\max_{x\in S^{n-1}}|P(x)|.$$
--
--   **Formalization Note** Written as a supremum; for $n\ge1$ the sphere is nonempty and compact, so the supremum is attained.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), p.3

import Mathlib
import Definitions.Def_SphereSOS_Rate_Sphere

namespace PolySphereLP

/-- **The sup norm `‖P‖_∞` on the sphere.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), p.3: `‖P‖_∞ =def max_{x∈S^{n−1}} |P(x)|`.

`supNorm n P = sup {|P(x)| : x ∈ S^{n−1}}`.

**Formalization Note.** For `n ≥ 1` the sphere is nonempty and compact and `x ↦ |P(x)|` is
continuous, so the supremum is a maximum and attained; the real `sSup` is never applied to an
empty or unbounded set in the items (all have `n ≥ 3`). -/
noncomputable def supNorm (n : ℕ) (P : MvPolynomial (Fin n) ℝ) : ℝ :=
  sSup ((fun x => |MvPolynomial.eval x P|) '' SphereSOS.Rate.sphere n)

end PolySphereLP


